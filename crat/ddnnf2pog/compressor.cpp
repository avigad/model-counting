/*========================================================================
  Copyright (c) 2022, 2023 Randal E. Bryant, Carnegie Mellon University
  
  Permission is hereby granted, free of charge, to any person
  obtaining a copy of this software and associated documentation files
  (the "Software"), to deal in the Software without restriction,
  including without limitation the rights to use, copy, modify, merge,
  publish, distribute, sublicense, and/or sell copies of the Software,
  and to permit persons to whom the Software is furnished to do so,
  subject to the following conditions:
  
  The above copyright notice and this permission notice shall be
  included in all copies or substantial portions of the Software.
  
  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
  EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
  MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
  NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS
  BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN
  ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
  CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
  SOFTWARE.
  ========================================================================*/

// Compress sequence of signed integers into a zero-terminated sequence of uint8's

#include <string.h>
#include "compressor.hh"

// Borrowed from Stack Overflow post by Nik Bougalis 10 Nov 2012
uint64_t hash_bytes(uint8_t *bytes) {
    uint64_t P1 =  104395301UL;
    uint64_t P2 = 2654435789UL;
    uint64_t val = P1;
    uint8_t b;
    while ((b = *bytes++) != 0) {
	val = (b * P2) + (val >> 23);
    }
    return val ^ (val << 37);
}

// Compare two zero-terminated byte sequences up to maximum length
bool byte_match(uint8_t *bytes1, uint8_t *bytes2, size_t maxlen) {
    return bcmp(bytes1, bytes2, maxlen);
}

// Convert between signed and unsigned representations
#define S2U(x) ((x) < 0 ? 2*(-(x))+1 : 2*(x))
#define U2S(u) (((u)&0x1)?-((u)>>1):(u)>>1)

/* Read byte sequence to get integer value */
/* Return number of bytes read, or -1 if invalid */
static int bytes2int(uint8_t *bytes, int *value) {
    unsigned int uval = 0;
    int count = 0;
    bool done = false;
    while (!done) {
	uint8_t nbyte = bytes[count++];
	uint8_t bval = (nbyte) & 0x7F;
	uint8_t hval = (bval>>7) & 0x1;
	uval = (uval << 7) + bval;
	done = (hval != 1);
    }
    *value = U2S(uval);
    return count;
}

/* Convert integer to byte representation */
static void int2bytes(byte_vector_t &dvec, int value) {
    unsigned int uval = S2U(value);
    uint8_t nbyte = uval & 0x7F;
    uval = uval >> 7;
    while (uval) {
	dvec.push_back((1 << 7) + nbyte);
	nbyte = uval & 0x7F;	
	uval = uval >> 7;
    }
    dvec.push_back(nbyte);
}

Compressor::Compressor() { }

void Compressor::start_compression() {
    compression_space.resize(0);
    decompression_space = NULL;
    terminated = false;
}

void Compressor::add(int val) {
    if (!terminated)
	int2bytes(compression_space, val);
    terminated = val == 0;
}

void Compressor::add(int count, int *vals) {
    while (count > 0) {
	add(*vals++);
	count--;
    }
}

void Compressor::add(std::vector<int> &vec) {
    for (int val : vec)
	add(val);
}

int Compressor::compressed_size() {
    // Allow extra byte for terminator
    return compression_space.size() + (terminated ? 0 : 1);
}

void Compressor::terminate() {
    add(0);
}

void Compressor::emit(uint8_t *dest) {
    terminate();
    memcpy(dest, compression_space.data(), compression_space.size());
}

void Compressor::emit(byte_vector_t &dest) {
    dest.resize(compression_space.size());
    emit(dest.data());
}

uint64_t Compressor::hash() {
    terminate();
    return hash_bytes(compression_space.data());
}

bool Compressor::matches(uint8_t *bytes) {
    terminate();
    return byte_match(bytes, compression_space.data(), compression_space.size());
}

void Compressor::start_decompression(uint8_t *bytes) {
    decompression_space = bytes;
}

void Compressor::extract(int *dest) {
    int count = bytes2int(decompression_space, dest);
    decompression_space += count;
}

void Compressor::extract(std::vector<int> &dest) {
    int val;
    while (true) {
	extract(&val);
	if (val == 0)
	    return;
	else
	    dest.push_back(val);
    }
    return;
}
