// No support for macros/ifdefs inside port definitions

module foo;
    `ifdef LABEL_A
    CHIP CPU (
        .clkin(clkin),
        `ifdef LABEL_B
        .bclko(bclko),
        `endif
        .cmode(cmode),
    );
endmodule
