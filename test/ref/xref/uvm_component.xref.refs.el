((#s(xref-match-item
     #("typedef class uvm_objection;" 14 27
       (face verilog-ext-xref-match-face))
     #s(xref-file-location "uvm_component.svh" 32 14)
     13)
    #s(xref-match-item
       #("  virtual function void raised (uvm_objection objection, uvm_object source_obj," 32 45
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 818 32)
       13)
    #s(xref-match-item
       #("  virtual function void dropped (uvm_objection objection, uvm_object source_obj," 33 46
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 833 33)
       13)
    #s(xref-match-item
       #("  virtual task all_dropped (uvm_objection objection, uvm_object source_obj," 28 41
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 848 28)
       13))
 (#s(xref-match-item
     #("  extern function new (string name, uvm_component parent);" 36 49
       (face verilog-ext-xref-match-face))
     #s(xref-file-location "uvm_component.svh" 66 36)
     13)
    #s(xref-match-item
       #("  extern virtual function uvm_component get_parent ();" 26 39
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 83 26)
       13)
    #s(xref-match-item
       #("  extern function void get_children(ref uvm_component children[$]);" 40 53
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 107 40)
       13)
    #s(xref-match-item
       #("  extern function uvm_component get_child (string name);" 18 31
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 112 18)
       13)
    #s(xref-match-item
       #("  extern function uvm_component lookup (string name);" 18 31
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 169 18)
       13)
    #s(xref-match-item
       #("  extern function uvm_component create_component (string requested_type_name," 18 31
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 881 18)
       13)
    #s(xref-match-item
       #("  /*protected*/ uvm_component m_parent;" 16 29
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 1388 16)
       13)
    #s(xref-match-item
       #("  protected     uvm_component m_children[string];" 16 29
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 1389 16)
       13)
    #s(xref-match-item
       #("  protected     uvm_component m_children_by_handle[uvm_component];" 16 29
	 (face verilog-ext-xref-match-face)
	 51 64
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 1390 51)
       13)
    #s(xref-match-item
       #("  extern protected virtual function bit  m_add_child(uvm_component child);" 53 66
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 1391 53)
       13)
    #s(xref-match-item
       #("  typedef uvm_abstract_component_registry#(uvm_component, \"uvm_component\") type_id;" 43 56
	 (face verilog-ext-xref-match-face)
	 59 72
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 1416 43)
       13)
    #s(xref-match-item
       #("endclass : uvm_component" 11 24
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 1461 11)
       13)
    #s(xref-match-item
       #("function uvm_component::new (string name, uvm_component parent);" 9 22
	 (face verilog-ext-xref-match-face)
	 42 55
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 1480 42)
       13)
    #s(xref-match-item
       #("function bit uvm_component::m_add_child(uvm_component child);" 13 26
	 (face verilog-ext-xref-match-face)
	 40 53
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 1574 40)
       13)
    #s(xref-match-item
       #("function void uvm_component::get_children(ref uvm_component children[$]);" 14 27
	 (face verilog-ext-xref-match-face)
	 46 59
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 1610 46)
       13)
    #s(xref-match-item
       #("function int uvm_component::get_first_child(ref string name);" 13 26
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 1619 13)
       13)
    #s(xref-match-item
       #("function int uvm_component::get_next_child(ref string name);" 13 26
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 1627 13)
       13)
    #s(xref-match-item
       #("function uvm_component uvm_component::get_child(string name);" 9 22
	 (face verilog-ext-xref-match-face)
	 23 36
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 1635 23)
       13)
    #s(xref-match-item
       #("function int uvm_component::has_child(string name);" 13 26
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 1647 13)
       13)
    #s(xref-match-item
       #("function int uvm_component::get_num_children();" 13 26
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 1655 13)
       13)
    #s(xref-match-item
       #("function string uvm_component::get_full_name ();" 16 29
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 1663 16)
       13)
    #s(xref-match-item
       #("function uvm_component uvm_component::get_parent ();" 9 22
	 (face verilog-ext-xref-match-face)
	 23 36
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 1676 23)
       13)
    #s(xref-match-item
       #("function void uvm_component::set_name (string name);" 14 27
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 1684 14)
       13)
    #s(xref-match-item
       #("function void uvm_component::m_set_full_name();" 14 27
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 1698 14)
       13)
    #s(xref-match-item
       #("    uvm_component tmp;" 4 17
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 1706 4)
       13)
    #s(xref-match-item
       #("function uvm_component uvm_component::lookup( string name );" 9 22
	 (face verilog-ext-xref-match-face)
	 23 36
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 1717 23)
       13)
    #s(xref-match-item
       #("  uvm_component comp;" 2 15
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 1720 2)
       13)
    #s(xref-match-item
       #("function int unsigned uvm_component::get_depth();" 22 35
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 1763 22)
       13)
    #s(xref-match-item
       #("function void uvm_component::m_extract_name(input string name ," 14 27
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 1774 14)
       13)
    #s(xref-match-item
       #("function void uvm_component::flush();" 14 27
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 1802 14)
       13)
    #s(xref-match-item
       #("function void uvm_component::do_flush();" 14 27
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 1810 14)
       13)
    #s(xref-match-item
       #("function uvm_object  uvm_component::create (string name =\"\");" 21 34
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 1828 21)
       13)
    #s(xref-match-item
       #("function uvm_object  uvm_component::clone ();" 21 34
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 1838 21)
       13)
    #s(xref-match-item
       #("function void  uvm_component::print_override_info (string requested_type_name," 15 28
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 1847 15)
       13)
    #s(xref-match-item
       #("function uvm_component uvm_component::create_component (string requested_type_name," 9 22
	 (face verilog-ext-xref-match-face)
	 23 36
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 1858 23)
       13)
    #s(xref-match-item
       #("function uvm_object uvm_component::create_object (string requested_type_name," 20 33
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 1870 20)
       13)
    #s(xref-match-item
       #("function void uvm_component::set_type_override (string original_type_name," 14 27
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 1882 14)
       13)
    #s(xref-match-item
       #("function void uvm_component::set_type_override_by_type (uvm_object_wrapper original_type," 14 27
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 1894 14)
       13)
    #s(xref-match-item
       #("function void  uvm_component::set_inst_override (string relative_inst_path," 15 28
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 1906 15)
       13)
    #s(xref-match-item
       #("function void uvm_component::set_inst_override_by_type (string relative_inst_path," 14 27
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 1928 14)
       13)
    #s(xref-match-item
       #("function void uvm_component::set_report_id_verbosity_hier( string id, int verbosity);" 14 27
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 1955 14)
       13)
    #s(xref-match-item
       #("function void uvm_component::set_report_severity_id_verbosity_hier( uvm_severity severity," 14 27
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 1965 14)
       13)
    #s(xref-match-item
       #("function void uvm_component::set_report_severity_action_hier( uvm_severity severity," 14 27
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 1977 14)
       13)
    #s(xref-match-item
       #("function void uvm_component::set_report_id_action_hier( string id, uvm_action action);" 14 27
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 1988 14)
       13)
    #s(xref-match-item
       #("function void uvm_component::set_report_severity_id_action_hier( uvm_severity severity," 14 27
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 1998 14)
       13)
    #s(xref-match-item
       #("function void uvm_component::set_report_severity_file_hier( uvm_severity severity," 14 27
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 2010 14)
       13)
    #s(xref-match-item
       #("function void uvm_component::set_report_default_file_hier( UVM_FILE file);" 14 27
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 2021 14)
       13)
    #s(xref-match-item
       #("function void uvm_component::set_report_id_file_hier( string id, UVM_FILE file);" 14 27
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 2031 14)
       13)
    #s(xref-match-item
       #("function void uvm_component::set_report_severity_id_file_hier ( uvm_severity severity," 14 27
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 2041 14)
       13)
    #s(xref-match-item
       #("function void uvm_component::set_report_verbosity_level_hier(int verbosity);" 14 27
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 2053 14)
       13)
    #s(xref-match-item
       #("function void uvm_component::build_phase(uvm_phase phase);" 14 27
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 2073 14)
       13)
    #s(xref-match-item
       #("function void uvm_component::connect_phase(uvm_phase phase);" 14 27
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 2083 14)
       13)
    #s(xref-match-item
       #("function void uvm_component::start_of_simulation_phase(uvm_phase phase);" 14 27
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 2087 14)
       13)
    #s(xref-match-item
       #("function void uvm_component::end_of_elaboration_phase(uvm_phase phase);" 14 27
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 2091 14)
       13)
    #s(xref-match-item
       #("task          uvm_component::run_phase(uvm_phase phase);" 14 27
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 2095 14)
       13)
    #s(xref-match-item
       #("function void uvm_component::extract_phase(uvm_phase phase);" 14 27
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 2099 14)
       13)
    #s(xref-match-item
       #("function void uvm_component::check_phase(uvm_phase phase);" 14 27
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 2103 14)
       13)
    #s(xref-match-item
       #("function void uvm_component::report_phase(uvm_phase phase);" 14 27
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 2107 14)
       13)
    #s(xref-match-item
       #("function void uvm_component::final_phase(uvm_phase phase);         return; endfunction" 14 27
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 2111 14)
       13)
    #s(xref-match-item
       #("task uvm_component::pre_reset_phase(uvm_phase phase);      return; endtask" 5 18
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 2115 5)
       13)
    #s(xref-match-item
       #("task uvm_component::reset_phase(uvm_phase phase);          return; endtask" 5 18
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 2116 5)
       13)
    #s(xref-match-item
       #("task uvm_component::post_reset_phase(uvm_phase phase);     return; endtask" 5 18
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 2117 5)
       13)
    #s(xref-match-item
       #("task uvm_component::pre_configure_phase(uvm_phase phase);  return; endtask" 5 18
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 2118 5)
       13)
    #s(xref-match-item
       #("task uvm_component::configure_phase(uvm_phase phase);      return; endtask" 5 18
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 2119 5)
       13)
    #s(xref-match-item
       #("task uvm_component::post_configure_phase(uvm_phase phase); return; endtask" 5 18
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 2120 5)
       13)
    #s(xref-match-item
       #("task uvm_component::pre_main_phase(uvm_phase phase);       return; endtask" 5 18
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 2121 5)
       13)
    #s(xref-match-item
       #("task uvm_component::main_phase(uvm_phase phase);           return; endtask" 5 18
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 2122 5)
       13)
    #s(xref-match-item
       #("task uvm_component::post_main_phase(uvm_phase phase);      return; endtask" 5 18
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 2123 5)
       13)
    #s(xref-match-item
       #("task uvm_component::pre_shutdown_phase(uvm_phase phase);   return; endtask" 5 18
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 2124 5)
       13)
    #s(xref-match-item
       #("task uvm_component::shutdown_phase(uvm_phase phase);       return; endtask" 5 18
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 2125 5)
       13)
    #s(xref-match-item
       #("task uvm_component::post_shutdown_phase(uvm_phase phase);  return; endtask" 5 18
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 2126 5)
       13)
    #s(xref-match-item
       #("function void uvm_component::phase_started(uvm_phase phase);" 14 27
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 2141 14)
       13)
    #s(xref-match-item
       #("function void uvm_component::phase_ended(uvm_phase phase);" 14 27
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 2147 14)
       13)
    #s(xref-match-item
       #("function void uvm_component::phase_ready_to_end (uvm_phase phase);" 14 27
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 2154 14)
       13)
    #s(xref-match-item
       #("function void uvm_component::define_domain(uvm_domain domain);" 14 27
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 2168 14)
       13)
    #s(xref-match-item
       #("function void uvm_component::set_domain(uvm_domain domain, int hier=1);" 14 27
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 2192 14)
       13)
    #s(xref-match-item
       #("function uvm_domain uvm_component::get_domain();" 20 33
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 2205 20)
       13)
    #s(xref-match-item
       #("task uvm_component::suspend();" 5 18
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 2216 5)
       13)
    #s(xref-match-item
       #("task uvm_component::resume();" 5 18
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 2224 5)
       13)
    #s(xref-match-item
       #("function void uvm_component::resolve_bindings();" 14 27
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 2232 14)
       13)
    #s(xref-match-item
       #("function void uvm_component::do_resolve_bindings();" 14 27
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 2240 14)
       13)
    #s(xref-match-item
       #("function void uvm_component::accept_tr (uvm_transaction tr," 14 27
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 2257 14)
       13)
    #s(xref-match-item
       #("function int uvm_component::begin_tr (uvm_transaction tr," 13 26
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 2274 13)
       13)
    #s(xref-match-item
       #("   function uvm_tr_database uvm_component::get_tr_database();" 28 41
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 2285 28)
       13)
    #s(xref-match-item
       #("   function void uvm_component::set_tr_database(uvm_tr_database db);" 17 30
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 2295 17)
       13)
    #s(xref-match-item
       #("function uvm_tr_stream uvm_component::get_tr_stream( string name," 23 36
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 2302 23)
       13)
    #s(xref-match-item
       #("function void uvm_component::free_tr_stream(uvm_tr_stream stream);" 14 27
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 2312 14)
       13)
    #s(xref-match-item
       #("function int uvm_component::m_begin_tr (uvm_transaction tr," 13 26
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 2340 13)
       13)
    #s(xref-match-item
       #("function void uvm_component::end_tr (uvm_transaction tr," 14 27
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 2437 14)
       13)
    #s(xref-match-item
       #("function int uvm_component::record_error_tr (string stream_name=\"main\"," 13 26
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 2477 13)
       13)
    #s(xref-match-item
       #("function int uvm_component::record_event_tr (string stream_name=\"main\"," 13 26
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 2531 13)
       13)
    #s(xref-match-item
       #("function void uvm_component::do_accept_tr (uvm_transaction tr);" 14 27
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 2583 14)
       13)
    #s(xref-match-item
       #("function void uvm_component::do_begin_tr (uvm_transaction tr," 14 27
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 2591 14)
       13)
    #s(xref-match-item
       #("function void uvm_component::do_end_tr (uvm_transaction tr," 14 27
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 2601 14)
       13)
    #s(xref-match-item
       #("function string uvm_component::massage_scope(string scope);" 16 29
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 2614 16)
       13)
    #s(xref-match-item
       #("function bit uvm_component::use_automatic_config();" 13 26
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 2638 13)
       13)
    #s(xref-match-item
       #("function void uvm_component::apply_config_settings (bit verbose=0);" 14 27
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 2645 14)
       13)
    #s(xref-match-item
       #("function void uvm_component::print_config(bit recurse = 0, audit = 0);" 14 27
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 2679 14)
       13)
    #s(xref-match-item
       #("    uvm_component c;" 4 17
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 2687 4)
       13)
    #s(xref-match-item
       #("function void uvm_component::print_config_with_audit(bit recurse = 0);" 14 27
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 2699 14)
       13)
    #s(xref-match-item
       #("function bit uvm_component::get_recording_enabled();" 13 26
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 2703 13)
       13)
    #s(xref-match-item
       #("function void uvm_component::set_recording_enabled(bit enabled);" 14 27
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 2707 14)
       13)
    #s(xref-match-item
       #("function void uvm_component::set_recording_enabled_hier(bit enabled);" 14 27
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 2714 14)
       13)
    #s(xref-match-item
       #("function void uvm_component::do_print(uvm_printer printer);" 14 27
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 2724 14)
       13)
    #s(xref-match-item
       #("function void uvm_component::do_execute_op( uvm_field_op op );" 14 27
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 2744 14)
       13)
    #s(xref-match-item
       #("      uvm_component child_comp;" 6 19
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 2747 6)
       13)
    #s(xref-match-item
       #("function void uvm_component::set_local(uvm_resource_base rsrc) ;" 14 27
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 2765 14)
       13)
    #s(xref-match-item
       #("function void uvm_component::m_unsupported_set_local(uvm_resource_base rsrc);" 14 27
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 2786 14)
       13)
    #s(xref-match-item
       #("function void uvm_component::m_set_cl_msg_args;" 14 27
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 2800 14)
       13)
    #s(xref-match-item
       #("function void uvm_component::m_set_cl_verb;" 14 27
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 2821 14)
       13)
    #s(xref-match-item
       #("function void uvm_component::m_set_cl_action;" 14 27
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 2855 14)
       13)
    #s(xref-match-item
       #("function void uvm_component::m_set_cl_sev;" 14 27
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 2895 14)
       13)
    #s(xref-match-item
       #("function void uvm_component::m_apply_verbosity_settings(uvm_phase phase);" 14 27
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 2934 14)
       13)
    #s(xref-match-item
       #("function void uvm_component::m_do_pre_abort;" 14 27
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 2958 14)
       13)
    #s(xref-match-item
       #("        function new(string name=\"asdf\", uvm_component parent);" 41 54
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "../github/verilog_ext_3.sv" 9 41)
       13))
 (#s(xref-match-item
     #("      beat = new;" 13 16
       (face verilog-ext-xref-match-face))
     #s(xref-file-location "axi_test.sv" 504 13)
     3)
    #s(xref-match-item
       #("      beat = new;" 13 16
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "axi_test.sv" 528 13)
       3)
    #s(xref-match-item
       #("      beat = new;" 13 16
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "axi_test.sv" 544 13)
       3)
    #s(xref-match-item
       #("      beat = new;" 13 16
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "axi_test.sv" 559 13)
       3)
    #s(xref-match-item
       #("      beat = new;" 13 16
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "axi_test.sv" 583 13)
       3)
    #s(xref-match-item
       #("      beat = new;" 13 16
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "axi_test.sv" 599 13)
       3)
    #s(xref-match-item
       #("      beat = new;" 13 16
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "axi_test.sv" 621 13)
       3)
    #s(xref-match-item
       #("      beat = new;" 13 16
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "axi_test.sv" 635 13)
       3)
    #s(xref-match-item
       #("      beat = new;" 13 16
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "axi_test.sv" 648 13)
       3)
    #s(xref-match-item
       #("      beat = new;" 13 16
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "axi_test.sv" 670 13)
       3)
    #s(xref-match-item
       #("      this.drv = new(axi);" 17 20
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "axi_test.sv" 780 17)
       3)
    #s(xref-match-item
       #("      this.cnt_sem = new(1);" 21 24
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "axi_test.sv" 781 21)
       3)
    #s(xref-match-item
       #("      automatic ax_beat_t ax_beat = new;" 36 39
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "axi_test.sv" 820 36)
       3)
    #s(xref-match-item
       #("          automatic w_beat_t w_beat = new;" 38 41
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "axi_test.sv" 1193 38)
       3)
    #s(xref-match-item
       #("      this.drv = new(axi);" 17 20
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "axi_test.sv" 1313 17)
       3)
    #s(xref-match-item
       #("      this.ar_queue = new;" 22 25
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "axi_test.sv" 1314 22)
       3)
    #s(xref-match-item
       #("        automatic r_beat_t  r_beat = new;" 37 40
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "axi_test.sv" 1353 37)
       3)
    #s(xref-match-item
       #("        automatic b_beat_t b_beat = new;" 36 39
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "axi_test.sv" 1454 36)
       3)
    #s(xref-match-item
       #("      this.drv  = new(axi);" 18 21
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "axi_test.sv" 1535 18)
       3)
    #s(xref-match-item
       #("      this.drv = new(axi);" 17 20
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "axi_test.sv" 1698 17)
       3)
    #s(xref-match-item
       #("    mailbox aw_mbx = new, w_mbx = new, b_mbx = new," 21 24
	 (face verilog-ext-xref-match-face)
	 34 37
	 (face verilog-ext-xref-match-face)
	 47 50
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "axi_test.sv" 1816 47)
       3)
    #s(xref-match-item
       #("            ar_mbx = new, r_mbx = new;" 21 24
	 (face verilog-ext-xref-match-face)
	 34 37
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "axi_test.sv" 1817 34)
       3)
    #s(xref-match-item
       #("      this.drv = new(axi);" 17 20
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "axi_test.sv" 1827 17)
       3)
    #s(xref-match-item
       #("        beat_addresses = new[aw_beat.ax_len + 1];" 25 28
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "axi_test.sv" 1979 25)
       3)
    #s(xref-match-item
       #("          aw_beat           = new;" 30 33
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "axi_test.sv" 2099 30)
       3)
    #s(xref-match-item
       #("          w_beat        = new;" 26 29
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "axi_test.sv" 2124 26)
       3)
    #s(xref-match-item
       #("          b_beat        = new;" 26 29
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "axi_test.sv" 2141 26)
       3)
    #s(xref-match-item
       #("          ar_beat           = new;" 30 33
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "axi_test.sv" 2157 30)
       3)
    #s(xref-match-item
       #("          r_beat        = new;" 26 29
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "axi_test.sv" 2182 26)
       3)
    #s(xref-match-item
       #("  super.new(name);" 8 11
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 1485 8)
       3)
    #s(xref-match-item
       #("  event_pool = new(\"event_pool\");" 15 18
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 1552 15)
       3)
    #s(xref-match-item
       #("    schedule = new(\"uvm_sched\", UVM_PHASE_SCHEDULE);" 15 18
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 2174 15)
       3)
    #s(xref-match-item
       #("            super.new(name, parent);" 18 21
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "../github/verilog_ext_3.sv" 10 18)
       3)
    #s(xref-match-item
       #("        endfunction : new" 22 25
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "../github/verilog_ext_3.sv" 11 22)
       3))
 nil
 (#s(xref-match-item
     #("  if(m_name == \"\")" 5 11
       (face verilog-ext-xref-match-face))
     #s(xref-file-location "uvm_component.svh" 1666 5)
     6)
    #s(xref-match-item
       #("    return m_name;" 11 17
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 1669 11)
       6)
    #s(xref-match-item
       #("  if(m_name != \"\") begin" 5 11
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 1685 5)
       6)
    #s(xref-match-item
       #("    m_name = get_name();" 4 10
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 1701 4)
       6)
    #s(xref-match-item
       #("    m_name = {m_parent.get_full_name(), \".\", get_name()};" 4 10
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 1703 4)
       6)
    #s(xref-match-item
       #("  if(m_name == \"\") return 0;" 5 11
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 1764 5)
       6)
    #s(xref-match-item
       #("  foreach(m_name[i])" 10 16
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 1766 10)
       6)
    #s(xref-match-item
       #("    if(m_name[i] == \".\") ++get_depth;" 7 13
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 1767 7)
       6))
 (#s(xref-match-item
     #("          m_verbosity_settings.push_back(setting);" 10 30
       (face verilog-ext-xref-match-face))
     #s(xref-file-location "uvm_component.svh" 2845 10)
     20)
    #s(xref-match-item
       #("  foreach (m_verbosity_settings[i]) begin" 11 31
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 2938 11)
       20)
    #s(xref-match-item
       #("    setting = m_verbosity_settings[i];" 14 34
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 2939 14)
       20)
    #s(xref-match-item
       #("      if(m_verbosity_settings[i].id == \"_ALL_\")" 9 29
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 2942 9)
       20)
    #s(xref-match-item
       #("        set_report_verbosity_level(m_verbosity_settings[i].verbosity);" 35 55
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 2943 35)
       20)
    #s(xref-match-item
       #("        set_report_id_verbosity(m_verbosity_settings[i].id, m_verbosity_settings[i].verbosity);" 32 52
	 (face verilog-ext-xref-match-face)
	 60 80
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 2945 60)
       20)
    #s(xref-match-item
       #("  m_verbosity_settings = remaining_settings;" 2 22
	 (face verilog-ext-xref-match-face))
       #s(xref-file-location "uvm_component.svh" 2951 2)
       20))
 (#s(xref-match-item
     #("    m_children[i].m_do_pre_abort();" 18 32
       (face verilog-ext-xref-match-face))
     #s(xref-file-location "uvm_component.svh" 2960 18)
     14)))
