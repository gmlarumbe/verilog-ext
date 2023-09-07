ERT_TESTS=test/scripts/ert-tests.sh


# DANGER: Workaround for v0.2.1 MELPA Stable Fix
package-el-melpa-stable: test_package_el
# End of DANGER

all: test_run

test: test_setup test_run

test_package_el: test_setup_pkg_el test_run_pkg_el

recompile: test_setup

test_setup:
	$(ERT_TESTS) recompile

test_run:
	$(ERT_TESTS) run_tests

test_setup_pkg_el:
	$(ERT_TESTS) recompile pkg_el

test_run_pkg_el:
	$(ERT_TESTS) run_tests t pkg_el

test_indent:
	$(ERT_TESTS) recompile_run indent::

test_beautify:
	$(ERT_TESTS) recompile_run beautify::

test_ts:
	$(ERT_TESTS) recompile_run tree-sitter::

gen_beautify:
	$(ERT_TESTS) recompile
	$(ERT_TESTS) gen_beautify_dir

gen_indent:
	$(ERT_TESTS) recompile
	$(ERT_TESTS) gen_indent_dir
	$(ERT_TESTS) gen_indent_dir treesit

gen_indent_ts:
	$(ERT_TESTS) recompile
	$(ERT_TESTS) gen_indent_dir treesit

gen_font_lock:
	$(ERT_TESTS) recompile
	$(ERT_TESTS) gen_font_lock

gen_font_lock_ts:
	$(ERT_TESTS) recompile
	$(ERT_TESTS) gen_font_lock treesit

