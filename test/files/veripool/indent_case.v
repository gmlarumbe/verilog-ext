module testcaseindent();
   case (a)
     1: begin
	asdf;
     end // case: 1
     
     2: begin
	asdfasdf;
     end // case: 2
     
     3: begin
	asdfasd;
     end // case: 3
     
   endcase // case (a)
   
   
   // TS: Added procedural block for unique/priority cases
    initial begin
   unique case (a)
     1: begin
	asdf;
     end // case: 1
     
     2: begin
	case (d)
	  2: a;
	  3: c;
	  4: begin
	     priority casex (f)
	       4: g;
	       5: h;
	     endcase // priority casex
	  end
	endcase // case (d)
	asdfasdf;
     end // case: 2
     
     3: begin
	asdfasd;
     end // case: 3
	  
	endcase // case (a)
   unique case (a)
     1: asdf;
     2: asdfasdf;
     3: asdfasd;
   endcase // case (a)
   
    end
   // TS: Added procedural block for unique/priority cases

endmodule // test_case_indent
