all: src/Main.hs
	stack build

generate: all
	./transform.sh data/current.json

configure:
	stack clean --full
	stack setup

clean:
	stack clean
	find -L . -name "*.swp" -exec rm -rf {} \;

