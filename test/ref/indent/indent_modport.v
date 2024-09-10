interface foo; // TS: Changed module to interface
    modport foo_mp(input a); // TS: Added a parameter list to remove syntax errors
    modport foo_mp1(a);
    modport foo_mp2(clocking bar_cb);
    logic a; // TS: Added a type for the declaration to remove syntax errors
endinterface // foo
