Lambda.exe: Main.hs Lambda.hs
	stack ghc -- -o $@ $<

run: Lambda.exe
	./Lambda.exe

clean:
	rm Lambda.exe

.PHONY: run clean
