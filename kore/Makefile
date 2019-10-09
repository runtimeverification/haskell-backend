package = kore

stack_yaml = STACK_YAML="../stack.yaml"
stack = $(stack_yaml) stack
pattern = ""

build:
	$(stack) build $(package)

build-dirty:
	$(stack) build --ghc-options=-fforce-recomp --pedantic $(package) --work-dir .stack-work-pedantic

run:
	$(stack) build --pedantic --fast --work-dir .stack-work-pedantic && $(stack) exec -- $(package)

install:
	$(stack) install

ghci:
	$(stack) ghci $(package)

test:
	$(stack) test $(package) --test-arguments "--hide-successes"

testp:
	$(stack) test --test-arguments '-p "$(pattern)"'

test-ghci:
	$(stack) ghci $(package):test:$(package)-test

pedantic:
	$(stack) build --haddock --no-haddock-deps --bench --no-run-benchmarks --test --no-run-tests --pedantic --work-dir .stack-work-pedantic

coverage:
	$(stack) test --coverage --work-dir .stack-work-coverage

ghcid:
	$(stack) exec -- ghcid -c "stack ghci $(package) --test --ghci-options='-fobject-code -fno-warn-unused-do-bind' --main-is $(package):kore-exec"

ghcid-repl:
	$(stack) exec -- ghcid -c "stack ghci $(package) --test --ghci-options='-fobject-code -fno-warn-unused-do-bind' --main-is $(package):kore-repl"


# TODO(Vladimir): remove 'hyperlink-source' when we upgrade from lts-12.10 (8.4.3)
hoogle-gen:
	$(stack) haddock; $(stack) hoogle generate --rebuild --no-haddock-hyperlink-source  -- --local

hoogle:
	$(stack) hoogle server -- --local --port 8000

dev-deps:
	stack install ghcid

tags:
	hasktags -e .

.PHONY: \
	build \
	run \
	install \
	ghci \
	test \
	testp \
	pedantic \
	coverage \
	ghcid \
	hoogle \
	tags
