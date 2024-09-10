module test;
    property p_test;
	a |-> b;
    endproperty : p_test
    assert property (p_test);
    a_test : assert property (p_test);

    // TS: Corrected syntax errors
    assign a  = b; // this and following lines are not properly indented
    logic foo;
endmodule // test
