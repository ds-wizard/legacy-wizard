all: app/Main.hs
	stack build

configure:
	rm -rf .stack-work
	stack clean
	stack setup

clean:
	stack clean
run: all
	stack exec DSServer
