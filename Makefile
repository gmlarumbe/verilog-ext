# Variables
ERT_TESTS=test/scripts/ert-tests.sh


# Main targets
all: test

test: test_setup test_run

test_package_el: test_setup_pkg_el test_run_pkg_el

recompile: test_setup


#  Tests setup/run
test_setup:
	$(ERT_TESTS) recompile

test_run:
	$(ERT_TESTS) run_tests

test_setup_pkg_el:
	$(ERT_TESTS) recompile pkg_el

test_run_pkg_el:
	$(ERT_TESTS) run_tests t pkg_el


# Regenerate expected outputs
gen_beautify: recompile
	$(ERT_TESTS) gen_beautify_dir

gen_indent: recompile
	$(ERT_TESTS) gen_indent_dir
	$(ERT_TESTS) gen_indent_dir treesit

gen_indent_ts: recompile
	$(ERT_TESTS) gen_indent_dir treesit

gen_font_lock: recompile
	$(ERT_TESTS) gen_font_lock

gen_font_lock_ts: recompile
	$(ERT_TESTS) gen_font_lock treesit


# Specific subset of tests
test_indent:
	$(ERT_TESTS) recompile_run indent::

test_beautify:
	$(ERT_TESTS) recompile_run beautify::

test_ts:
	$(ERT_TESTS) recompile_run tree-sitter::

subset:
	$(ERT_TESTS) recompile_run $(TESTS)
