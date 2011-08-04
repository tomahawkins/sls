.PHONY: all
all: inverter.v

nets.png: nets.neato
	neato -Tpng -o nets.png nets.neato

inverter.v: Test.hs
	runhaskell -W Test.hs

.PHONY: clean
clean:
	-rm *.png
	-rm *.v
	-rm *.yices

