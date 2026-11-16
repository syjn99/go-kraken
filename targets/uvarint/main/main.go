// Command uvarint keeps encoding/binary.Uvarint in the ELF as a separate symbol.
// The package variable takes the address of the function, so the linker keeps it.
package main

import (
	"encoding/binary"
	"os"
)

var decode = binary.Uvarint

func main() {
	x, n := decode([]byte(os.Args[0]))
	println(x, n)
}
