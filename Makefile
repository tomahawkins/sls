.PHONY: all
all: nets.png inverter.v

nets.png: nets.neato
	neato -Tpng -o nets.png nets.neato

inverter.v: Test.hs
	runhaskell -W Test.hs

.PHONY: clean
clean:
	-rm nets.png
	-rm *.v

