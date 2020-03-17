SOURCES=$(wildcard *.hs)
EXE=Lambda.exe

$(EXE): $(SOURCES) Makefile
	stack ghc -- -O -o $@ $(SOURCES)

run: $(EXE)
	./$(EXE)

clean:
	rm $(EXE) *.o

.PHONY: run clean
