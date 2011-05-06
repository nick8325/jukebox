all: jukebox

.PHONY: jukebox
jukebox: clean1
	cabal install --bindir=.
	cp dist/build/jukebox/jukebox-tmp/* .

clean: clean1
	cabal clean

clean1:
	rm -f *.hi *.o jukebox Lexer.hs
