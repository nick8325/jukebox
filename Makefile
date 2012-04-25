all: jukebox

.PHONY: jukebox
jukebox: clean1
	auto=1 scripts/install-minisat
	LD_LIBRARY_PATH=$(shell scripts/find-minisat) \
	DYLD_LIBRARY_PATH=$(shell scripts/find-minisat) \
	cabal install --bindir=. --ghc-options="-rtsopts -with-rtsopts=-K64M"
	ln -sf ../dist/build/jukebox/jukebox-tmp/TPTP/Lexer.hs TPTP

clean: clean1
	cabal clean

clean1:
	rm -f *.hi *.o jukebox Lexer.hs
