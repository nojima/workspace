SOURCES=$(wildcard *.hs)

Lambda.exe: $(SOURCES) Makefile
	stack ghc -- -O -o $@ $(SOURCES)

run: Lambda.exe
	./Lambda.exe

clean:
	rm Lambda.exe

.PHONY: run clean
