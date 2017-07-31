all: Main.hs ../Transform/dist/Questionnaire.hs
	hastec Main.hs -o ../DSServer/static/js/main.js -Wall -Wincomplete-uni-patterns -Wincomplete-record-updates -Wmissing-import-lists --debug

production: Main.hs ../Transform/dist/Questionnaire.hs
	make clean
	hastec Main.hs -o ../DSServer/static/js/main.js -Wall -Wincomplete-uni-patterns -Wincomplete-record-updates -Wmissing-import-lists --opt-all

clean:
	find -L . -name "*.o" -exec rm -rf {} \;
	find -L . -name "*.hi" -exec rm -rf {} \;
	find -L . -name "*.jsmod" -exec rm -rf {} \;
	find -L . -name "*.swp" -exec rm -rf {} \;
	rm -f ../DSServer/static/js/main.js
