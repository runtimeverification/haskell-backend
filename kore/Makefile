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
	$(stack) test $(package)

testp:
	$(stack) test --test-arguments '-p "$(pattern)"'

test-ghci:
	$(stack) ghci $(package):test:$(package)-test

fast:
	$(stack) install --fast --test --no-run-tests --work-dir=.stack-work-fast

fast-test:
	$(stack) build --fast --test --work-dir=.stack-work-fast

pedantic:
	$(stack) build --haddock --no-haddock-deps --bench --no-run-benchmarks --test --no-run-tests --pedantic --work-dir .stack-work-pedantic

coverage:
	$(stack) test --coverage --work-dir .stack-work-coverage

ghcid:
	$(stack) exec -- ghcid -c "stack ghci $(package) --test --work-dir .stack-work-ghci --ghci-options='-fobject-code -fno-warn-unused-do-bind' --main-is $(package):kore-exec"

ghcid-repl:
	$(stack) exec -- ghcid -c "stack ghci $(package) --test --ghci-options='-fobject-code -fno-warn-unused-do-bind' --main-is $(package):kore-repl --work-dir .stack-work-ghci"

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
