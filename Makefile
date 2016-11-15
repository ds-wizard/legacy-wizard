all: Main.hs
	ghc Transform/Main.hs
	./transform.sh data/example.json
	hastec Main.hs -o Page/js/main.js -Wall --debug

clean:
	find . -name "*.o" -exec rm -rf {} \;
	find . -name "*.hi" -exec rm -rf {} \;
	find . -name "*.jsmod" -exec rm -rf {} \;
	rm -f Transform/Main Page/js/main.js
