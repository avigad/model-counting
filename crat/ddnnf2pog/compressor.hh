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
// Rule: Cannot have any zero's in the uncompressed data

#pragma once

#include <cstdint>
#include <vector>

typedef std::vector<uint8_t> byte_vector_t;

// Useful hash function for zero-terminated byte sequences
uint64_t hash_bytes(uint8_t *bytes);

// Compare two zero-terminated byte sequences up to maximum length
bool byte_match(uint8_t *bytes1, uint8_t *bytes2, size_t maxlen);

class Compressor {
private:
    byte_vector_t compression_space;
    bool terminated;

    uint8_t *decompression_space;

public:
    Compressor();

    // COMPRESSION
    void start_compression();

    // Once add value 0, no other values will be added
    // It's best not to add 0 as regular data
    void add(int val);
    void add(int count, int *vals);
    void add(std::vector<int> &vec);

    // Add terminating zero
    void terminate();

    // What would size be if terminated now?
    int compressed_size();

    // Terminate, if necessary, and copy compressed bytes to destination
    void emit(uint8_t *dest);
    void emit(byte_vector_t &dest);

    // Terminate, if necessary, and compute hash over compressed bytes
    uint64_t hash();

    // Compare compressed bytes to other byte sequence
    bool matches(uint8_t *bytes);

    // DECOMPRESSION
    void start_decompression(uint8_t *bytes);

    void extract(int *dest);

    void extract(std::vector<int> &dest);

};
