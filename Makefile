ERT_TESTS=test/scripts/ert-tests.sh

all: test

test: test_setup test_run

test_setup:
	$(ERT_TESTS) recompile

test_run:
	$(ERT_TESTS) run_tests

