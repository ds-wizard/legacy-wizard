all: app/Main.hs
	stack build

configure:
	stack clean --full
	stack setup

clean:
	stack clean

run: all
	stack exec DSServer
