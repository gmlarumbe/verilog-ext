// test/files/common/axi_test.sv:809
// Seems a grammar error with concatenation

    function void add_traffic_shaping(input int unsigned len, input int unsigned freq);
      if (traffic_shape.size() == 0)
        traffic_shape.push_back({len, freq});
      else
        traffic_shape.push_back({len, traffic_shape[$].cprob + freq});

      max_cprob = traffic_shape[$].cprob;
    endfunction : add_traffic_shaping
