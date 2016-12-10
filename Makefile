all: Main.hs Transform/dist/Questionnaire.hs
	cp Transform/dist/Questionnaire.hs .
	hastec Main.hs -o Page/js/main.js -Wall --debug

production: Main.hs Transform/dist/Questionnaire.hs
	hastec Main.hs -o Page/js/main.js -Wall --opt-all

clean:
	find . -name "*.o" -exec rm -rf {} \;
	find . -name "*.hi" -exec rm -rf {} \;
	find . -name "*.jsmod" -exec rm -rf {} \;
	rm -f Page/js/main.js
