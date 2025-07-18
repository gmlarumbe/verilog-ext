module foo;

    foo_module #(
        .G_SOME_CONSTANT            (5),
        .G_SOME_OTHER_CONSTANT      (5),
        .G_EVEN_SOME_OTHER_CONSTANT ()
    ) my_foo (
        .clk    (my_clk), // asdf
        .reset  (my_reset),

        // Comment regarding the ports below (because sometimes it's warranted)
        .port_a (my_a),   // asdf 2
        .port_b (my_b),   // asdf3

        //Another comment (with paren)
        .port_c (my_c),
        .port_d (my_d),

        // Some implicit port connections
        .port_e,
        .port_f
    );

endmodule
