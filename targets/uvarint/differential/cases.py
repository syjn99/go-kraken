#!/usr/bin/env python3
"""Write the differential case list of the uvarint target to standard output.

Usage: python3 -I -B cases.py > cases.txt
Each line is one input buffer as lowercase hexadecimal. The line `-` is the empty buffer.
The list is the same on each run and on each Python version. The script does not use the `random` module.
The script writes each buffer only once, at its first place.
"""
import sys


def encode(v):
    """The base-128 encoding of v, least significant group first."""
    out = []
    while v >= 0x80:
        out.append(v & 0x7F | 0x80)
        v >>= 7
    out.append(v)
    return out


class Lcg:
    """A linear congruential generator modulo 2^32 with a fixed seed."""

    def __init__(self, seed):
        self.state = seed

    def next(self):
        self.state = (1664525 * self.state + 1013904223) % 2 ** 32
        return self.state >> 8  # the low bits of this generator have short periods


def cases():
    out = [[]]
    # Each length from 1 to 12, with all bytes 0x80, and with all bytes 0xff.
    for n in range(1, 13):
        out += [[0x80] * n, [0xFF] * n]
    # Powers of two and the numbers one less, with and without two more bytes. Each buffer also without its last byte.
    for k in range(64):
        for v in (2 ** k, 2 ** k - 1):
            for buf in (encode(v), encode(v) + [0x01, 0x80]):
                out += [buf, buf[:-1]]
    # The ten-byte boundary.
    for last in (0x00, 0x01, 0x02, 0x7F, 0x80):
        out.append([0xFF] * 9 + [last])
    out.append([0x80] * 9 + [0x01])
    out.append([0x80] * 9 + [0x02])
    # Eleven and twelve bytes with continuation bits.
    out += [[0xFF] * 10 + [0x00], [0xFF] * 10 + [0x01], [0x80] * 10 + [0x00], [0x80] * 10 + [0x01],
            [0xFF] * 11 + [0x00], [0x80] * 11 + [0x00], [0x81] * 11 + [0x7F]]
    # Non-canonical encodings: zero groups at the end.
    out += [[0x80, 0x00], [0xFF, 0x00], [0x80, 0x80, 0x00], [0x81, 0x80, 0x00], [0xFF, 0x80, 0x00],
            [0x80] * 8 + [0x00], [0x80] * 9 + [0x00], [0xFF] * 8 + [0x80, 0x00], [0x80, 0x00, 0x00]]
    # Pseudo-random buffers of length 0 to 12. Three of four bytes get the continuation bit.
    # Thus most buffers get to the longer paths of the decoder.
    g = Lcg(20261116)
    for _ in range(400):
        n = g.next() % 13
        buf = []
        for _ in range(n):
            b = g.next() & 0xFF
            if g.next() % 4 != 0:
                b |= 0x80
            buf.append(b)
        out.append(buf)
    return out


def main():
    seen = set()
    for buf in cases():
        line = bytes(buf).hex() or "-"
        if line not in seen:
            seen.add(line)
            sys.stdout.write(line + "\n")


if __name__ == "__main__":
    main()
