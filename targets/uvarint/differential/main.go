// Command differential reads the uvarint case list on standard input.
// For each case it prints one line: the case as written, then x and n of binary.Uvarint.
// The line "-" is the empty buffer.
package main

import (
	"bufio"
	"encoding/binary"
	"encoding/hex"
	"fmt"
	"os"
)

func main() {
	in := bufio.NewScanner(os.Stdin)
	out := bufio.NewWriter(os.Stdout)
	defer out.Flush()
	for in.Scan() {
		line := in.Text()
		var buf []byte
		if line != "-" {
			b, err := hex.DecodeString(line)
			if err != nil || line == "" {
				fmt.Fprintf(os.Stderr, "bad case line: %q\n", line)
				out.Flush()
				os.Exit(1)
			}
			buf = b
		}
		x, n := binary.Uvarint(buf)
		fmt.Fprintf(out, "%s %d %d\n", line, x, n)
	}
	if err := in.Err(); err != nil {
		fmt.Fprintln(os.Stderr, err)
		out.Flush()
		os.Exit(1)
	}
}
