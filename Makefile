SHELL = /bin/bash

.PHONY: check clean help

help:
	@echo "Usage:"
	@echo "  make check    Typecheck all modules."
	@echo "  make clean    Remove all Agda artifacts."
	@echo "  make help     Show this message and exit."

check:
	. scripts/everything.sh Everything
	agda src/Everything.agda

clean:
	rm -rf _build
	rm -f src/Everything.agda
	find . -name "*.agda~" -type f -delete
