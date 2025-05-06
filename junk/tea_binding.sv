bind tea_accelerator tea_properties security_props(
    .i_clk(i_clk),
    .i_rst(i_rst),
    .state(state),
    .next_state(next_state),
    .round_counter(round_counter),
    .i_axis_valid_s(i_axis_valid_s),
    .o_axis_ready_s(o_axis_ready_s),
    .o_axis_valid_m(o_axis_valid_m),
    .i_axis_ready_m(i_axis_ready_m)
);