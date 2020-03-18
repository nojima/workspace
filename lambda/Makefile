SOURCES=$(wildcard *.hs)
BUILD_DIR=build
EXE=$(BUILD_DIR)/Lambda.exe

$(EXE): $(SOURCES) $(BUILD_DIR) Makefile
	stack ghc -- -O -outputdir $(BUILD_DIR) -o $@ $(SOURCES)

$(BUILD_DIR):
	mkdir -p $(BUILD_DIR)

run: $(EXE)
	./$(EXE)

clean:
	rm -r $(BUILD_DIR)

.PHONY: run clean
