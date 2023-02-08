ERT_TESTS=test/scripts/ert-tests.sh

all: test

test: test_setup test_run

recompile: test_setup

test_setup:
	$(ERT_TESTS) recompile

test_run:
	$(ERT_TESTS) run_tests

test_indent:
	$(ERT_TESTS) recompile_run indent::

test_beautify:
	$(ERT_TESTS) recompile_run beautify::

test_ts:
	$(ERT_TESTS) recompile_run tree-sitter::

update_beautify_dir:
	$(ERT_TESTS) recompile
	$(ERT_TESTS) update_beautify_dir

update_indent_dir:
	$(ERT_TESTS) recompile
	$(ERT_TESTS) update_indent_dir
	$(ERT_TESTS) update_indent_dir treesit

