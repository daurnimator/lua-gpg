-- RFC 4880
local basexx = require "basexx"

local function find_armour(c, pos)
	return c:find("%f[^%z\n]%-%-%-%-%-BEGIN PGP ([%w ]+)%-%-%-%-%-\r?%f[\n](.-)\r?\n\r?\n(.-)=(....)\r?\n%-%-%-%-%-END PGP %1%-%-%-%-%-", pos)
end

local function crc24(init, poly, c)
	local crc = init
	for l=1, #c do
		crc = crc ~ (c:byte(l) << 16)
		for _=1, 8 do
			crc = crc << 1
			if crc & 0x1000000 ~= 0 then
				crc = crc ~ poly
			end
		end
	end
	return crc & 0xFFFFFF
end

local function bytes2hex(str)
	return (str:gsub(".", function(c) return string.format("%02X", c:byte()) end))
end

local function dearmor(c)
	local _, _, t, header, body, checksum = find_armour(c)
	if not _ then return nil end

	local headers = {}
	for key, value in header:gmatch("%f[^%z\n]([^\n]-): ([^\n]+)") do
		-- TODO: duplicate headers
		headers[key] = value
	end

	body = body:gsub("[\r\n]", "") -- https://github.com/aiq/basexx/issues/4
	body = basexx.from_base64(body)

	checksum = basexx.from_base64(checksum)
	checksum = string.unpack(">I3", checksum)
	assert(crc24(0xB704CE, 0x864CFB, body) == checksum)
	return t, headers, body
end

local function read_packet(str, pos)
	local ptag = str:byte(pos)
	assert(ptag & 0x80 ~= 0)
	local tag, start, finish
	if ptag & 0x40 ~= 0 then
		-- new format
		tag = ptag & 0x3F
		local o1 = str:byte(pos+1)
		if o1 < 192 then
			start = pos + 2
			finish = pos - 1 + o1
		else
			error("NYI")
		end
		error("NYI")
	else
		tag = (ptag >> 2) & 0xF
		local len = ptag & 3
		if len == 0 then
			-- The packet has a one-octet length
			start = pos + 2
			finish = start - 1 + str:byte(pos+1)
		elseif len == 1 then
			-- The packet has a two-octet length
			start = pos + 3
			finish = start - 1 + string.unpack(">I2", str, pos+1)
		elseif len == 2 then
			-- The packet has a four-octet length
			start = pos + 5
			finish = start - 1 + string.unpack(">I4", str, pos+1)
		elseif len == 3 then
			--[[The packet is of indeterminate length.
			The header is 1 octet long, and the implementation must determine how long the packet is.
			If the packet is in a file, this means that the packetxtends until the end of the file.]]
			start = pos+1
			finish = #str
		end
	end
	return tag, start, finish
end

local function checkpos(pos, finish, inc)
	if finish - pos < inc then
		error("unexpected EOF")
	end
end

local function read_mpi(body, start, finish)
	checkpos(start, finish, 2)
	local len = string.unpack(">I2", body, start)
	local bytes = (len - 1) // 8 + 1
	checkpos(start, finish, bytes)
	return nil, start + 2 + bytes
end

local digest = require "openssl.digest"

local function read_public_key_packet(body, start, finish)
	print(":public key packet:")
	checkpos(start, finish, 1)
	local version = body:byte(start)
	local pos = start + 1
	local created, expires, algo
	if version == 3 then
		checkpos(pos, finish, 7)
		created, expires, algo = string.unpack(">I4I2B", body, pos)
		pos = pos + 7
	elseif version == 4 then
		checkpos(pos, finish, 5)
		created, algo = string.unpack(">I4B", body, pos)
		pos = pos + 5
	else
		error("unknown version")
	end
	print(string.format("\tversion %d, algo %d, created %d, expires %d", version, algo, created, expires or 0))
	local rsa_n, rsa_e
	if algo == 1 then -- RSA
		rsa_n, pos = read_mpi(body, pos, finish)
		-- print(string.format("\tpkey[0]: [%d bits]", rsa_n))
		rsa_e, pos = read_mpi(body, pos, finish)
		-- print(string.format("\tpkey[1]: [%d bits]", rsa_e))
		if pos-1 ~= finish then
			error("expected EOF")
		end
	else
		error("NYI")
	end
	local fingerprint_raw
	if version == 3 then
		--[[ The fingerprint of a V3 key is formed by hashing the body (but not
		the two-octet length) of the MPIs that form the key material (public
		modulus n, followed by exponent e) with MD5.]]
		if algo ~= 1 then
			error("algorithms other than 1 not supported for version 3 keys")
		end
		error("NYI")
	elseif version == 4 then
		--[[ A V4 fingerprint is the 160-bit SHA-1 hash of the octet 0x99,
		followed by the two-octet packet length, followed by the entire
		Public-Key packet starting with the version field.]]
		fingerprint_raw = digest.new("SHA1"):final("\x99",
			string.pack(">I2", finish - start + 1),
			body:sub(start, finish))
	else
		error("unknown version")
	end
	local fingerprint = bytes2hex(fingerprint_raw)
	print(string.format("\tkeyid: %s", fingerprint:sub(-16))) -- uses long key id format
end

local function read_signature_subpacket_frame(body, start, finish)
	checkpos(start, finish, 1)
	local o1 = body:byte(start)
	local pos, len
	if o1 < 192 then
		len = o1
		pos = start + 1
	elseif o1 < 255 then
		checkpos(start, finish, 2)
		len = (o1-192)<<8 + body:byte(2) + 192
		pos = start + 2
	else
		checkpos(start, finish, 5)
		len = string.unpack(">I4", body, 2)
		pos = start + 5
	end
	checkpos(pos, finish, 1)
	local typ = body:byte(pos)
	local critical = typ&0x80 ~= 0
	return typ&0x7F, critical, pos+1, pos+len-1
end

local function read_signature_subpacket(body, start, finish)
	local typ, critical, substart, subfinish = read_signature_subpacket_frame(body, start, finish)
	local packet = {
		type = typ;
		critical = critical;
		length = subfinish-substart+1;
	}
	if typ == 2  then -- Signature Creation Time
		packet.created = string.unpack(">I4", body, substart)
	-- elseif typ == 3 then -- Signature Expiration Time
	-- elseif typ == 4 then -- Exportable Certification
	-- elseif typ == 5 then -- Trust Signature
	-- elseif typ == 6 then -- Regular Expression
	-- elseif typ == 7 then -- Revocable
	elseif typ == 9 then -- Key Expiration Time
		packet.expires = string.unpack(">I4", body, substart)
	-- elseif typ == 10 then -- Placeholder for backward compatibility
	-- elseif typ == 11 then -- Preferred Symmetric Algorithms
	-- elseif typ == 12 then -- Revocation Key
	elseif typ == 16 then -- Issuer
		packet.issuer = string.unpack(">c8", body, substart)
	-- elseif typ == 20 then -- Notation Data
	-- elseif typ == 21 then -- Preferred Hash Algorithms
	-- elseif typ == 22 then -- Preferred Compression Algorithms
	-- elseif typ == 23 then -- Key Server Preferences
	-- elseif typ == 24 then -- Preferred Key Server
	-- elseif typ == 25 then -- Primary User ID
	-- elseif typ == 26 then -- Policy URI
	elseif typ == 27 then -- Key Flags
		local t = {}
		for i=substart, subfinish do
			t[body:byte(i)] = true
		end
		packet.key_flags = t
	-- elseif typ == 28 then -- Signer's User ID
	-- elseif typ == 29 then -- Reason for Revocation
	-- elseif typ == 30 then -- Features
	-- elseif typ == 31 then -- Signature Target
	-- elseif typ == 32 then -- Embedded Signature
	-- elseif typ >= 100 and typ < 110 then -- Private or experimental
	end
	return packet, subfinish+1
end

local function read_signature_subpackets(body, start, finish)
	local packets = {}
	local pos = start
	while pos < finish do
		local packet
		packet, pos = read_signature_subpacket(body, pos, finish)
		table.insert(packets, packet)
	end
	return packets
end

local function read_signature_packet(body, start, finish)
	checkpos(start, finish, 1)
	local version = body:byte(start)
	local pos = start + 1
	local sigclass, sigalgo, digest_algo
	local hashed_subpacket_start, hashed_subpacket_len
	local unhashed_subpacket_start, unhashed_subpacket_len
	if version == 3 then
		error("NYI")
	elseif version == 4 then
		checkpos(pos, finish, 3+2+2+2)
		sigclass, sigalgo, digest_algo, hashed_subpacket_len = string.unpack(">BBBI2", body, pos)
		pos = pos + 5
		hashed_subpacket_start = pos
		checkpos(pos, finish, hashed_subpacket_len+4)
		pos = pos + hashed_subpacket_len
		unhashed_subpacket_len = string.unpack(">I2", body, pos)
		pos = pos + 2
		unhashed_subpacket_start = pos
		checkpos(pos, finish, unhashed_subpacket_len+2)
		pos = pos + unhashed_subpacket_len

		-- print(sigclass, sigalgo, digest_algo, hashed_subpacket_len, unhashed_subpacket_len)
	else
		error("unknown version")
	end

	-- Two-octet field holding the left 16 bits of the signed hash value.
	local o1, o2 = body:byte(pos, pos+1)
	pos = pos + 2



	local hashed_subpackets = read_signature_subpackets(body, hashed_subpacket_start, hashed_subpacket_start+hashed_subpacket_len)
	local unhashed_subpackets = read_signature_subpackets(body, unhashed_subpacket_start, unhashed_subpacket_start+unhashed_subpacket_len)



	local created do
		for _, packet in ipairs(hashed_subpackets) do
			if packet.type == 2 then
				created = packet.created
				break
			end
		end
	end
	print(string.format(":signature packet: algo %d, keyid %s", sigalgo, keyid))
	print(string.format("\tversion %d, created %d, md5len %d, sigclass 0x%x", version, created, md5len or 0, sigclass))
	print(string.format("\tdigest algo %d, begin of digest %02x %02x", digest_algo, o1, o2))

	for _, k in ipairs{{hashed_subpackets, "\thashed "}, {unhashed_subpackets, "\t"}} do
		local packets, prefix = k[1], k[2]
		for _, packet in ipairs(packets) do
			local str
			if packet.type == 2 then -- Signature Creation Time
				str = "sig created "..os.date("!%Y-%m-%d", packet.created)
			-- elseif packet.type == 3 then -- Signature Expiration Time
			-- elseif packet.type == 4 then -- Exportable Certification
			-- elseif packet.type == 5 then -- Trust Signature
			-- elseif packet.type == 6 then -- Regular Expression
			-- elseif packet.type == 7 then -- Revocable
			elseif packet.type == 9 then -- Key Expiration Time
				local seconds = packet.expires
				-- TODO: special-case 0?
				str = string.format("key expires after %dy%dd%dh%dm",
					seconds // 31536000, -- seconds in a year: 365*86400
					seconds % 31536000 // 86400,
					seconds % 86400 // 3600,
					seconds % 3600 // 60)
			-- elseif packet.type == 10 then -- Placeholder for backward compatibility
			-- elseif packet.type == 11 then -- Preferred Symmetric Algorithms
			-- elseif packet.type == 12 then -- Revocation Key
			elseif packet.type == 16 then -- Issuer
				str = "issuer key ID " .. bytes2hex(packet.issuer)
			-- elseif packet.type == 20 then -- Notation Data
			-- elseif packet.type == 21 then -- Preferred Hash Algorithms
			-- elseif packet.type == 22 then -- Preferred Compression Algorithms
			-- elseif packet.type == 23 then -- Key Server Preferences
			-- elseif packet.type == 24 then -- Preferred Key Server
			-- elseif packet.type == 25 then -- Primary User ID
			-- elseif packet.type == 26 then -- Policy URI
			elseif packet.type == 27 then -- Key Flags
				local flags = {}
				for flag in pairs(packet.key_flags) do
					table.insert(flags, string.format("%x", flag))
				end
				table.sort(flags)
				str = "key flags: " .. table.concat(flags)
			end
			print(string.format("%ssubpkt %d len %d (%s)", prefix, packet.type, packet.length, str))
		end
	end
	-- print(string.format("\tdata: [%d bits]", ))
end


local f = assert(io.open(arg[1]))
local c = assert(f:read("*a"))
f:close()
local t, headers, body = dearmor(c)
assert(t == "PUBLIC KEY BLOCK")
-- print(body)
local pos = 1
while pos < #body do
	local tag, start, finish = read_packet(body, pos)
	print(string.format("# off=%d ctb=%x tag=%d hlen=%d plen=%d", pos-1, body:byte(pos), tag, start-pos, finish-start+1))
	if tag == 0 then -- Reserved - a packet tag MUST NOT have this value
	elseif tag == 1 then -- Public-Key Encrypted Session Key Packet
	elseif tag == 2 then -- Signature Packet
		read_signature_packet(body, start, finish)
	elseif tag == 3 then -- Symmetric-Key Encrypted Session Key Packet
	elseif tag == 4 then -- One-Pass Signature Packet
	elseif tag == 5 then -- Secret-Key Packet
	elseif tag == 6 then -- Public-Key Packet
		read_public_key_packet(body, start, finish)
	elseif tag == 7 then -- Secret-Subkey Packet
	elseif tag == 8 then -- Compressed Data Packet
	elseif tag == 9 then -- Symmetrically Encrypted Data Packet
	elseif tag == 10 then -- Marker Packet
	elseif tag == 11 then -- Literal Data Packet
	elseif tag == 12 then -- Trust Packet
	elseif tag == 13 then -- User ID Packet
		local uid = body:sub(start, finish)
		print(":user ID packet: \""..uid..'"')
	elseif tag == 14 then -- Public-Subkey Packet
	elseif tag == 17 then -- User Attribute Packet
	elseif tag == 18 then -- Sym. Encrypted and Integrity Protected Data Packet
	elseif tag == 19 then -- Modification Detection Code Packet
	elseif tag >= 60 then -- Private or Experimental Values
	else
		error("unknown packet type")
	end
	pos = finish + 1
end
