package = kore

stack_yaml = STACK_YAML="../../../../stack.yaml"
stack = $(stack_yaml) stack
pattern = ""

build:
	$(stack) build $(package)

build-dirty:
	$(stack) build --ghc-options=-fforce-recomp $(package)

run:
	$(stack) build --fast && $(stack) exec -- $(package)

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
	$(stack) build --haddock --no-haddock-deps --coverage --bench --no-run-benchmarks --test --no-run-tests --pedantic

ghcid:
	$(stack) exec -- ghcid -c "stack ghci $(package) --test --ghci-options='-fobject-code -fno-warn-unused-do-bind'"

dev-deps:
	stack install ghcid

.PHONY : build build-dirty run install ghci test test-ghci ghcid dev-deps
