all: jukebox

.PHONY: jukebox
jukebox: clean1
	cabal install --bindir=. --ghc-options="-rtsopts -with-rtsopts=-K64M"
	ln -sf ../dist/build/jukebox/jukebox-tmp/TPTP/Lexer.hs TPTP

clean: clean1
	cabal clean

clean1:
	rm -f *.hi *.o jukebox Lexer.hs
