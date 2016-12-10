all: src/Main.hs
	cabal build
	./transform.sh data/example.json

configure:
	rm -rf .cabal* cabal.sandbox.config dist
	cabal sandbox init
	cabal update
	cabal install --dependencies-only

clean:	
	rm -rf dist
