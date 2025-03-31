

# Overview of all composite scenarios

<table>
    <tbody>
        <tr><th>Scenario</th><th>Scenario Type</th><th>Subscenario</th><th>Subscenario type</th><th>Initiators</th><th>Targets</th><th>Operation</th><th>Efficiency</th></tr>
        <tr><td rowspan=2>1xAIC_RD_1xSDMA_RD_L2</td><td rowspan=2>composite</td><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td rowspan=2>1xAIC_RD_1xSDMA_WR_L2</td><td rowspan=2>composite</td><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td rowspan=2>1xAIC_WR_1xSDMA_WR_L2</td><td rowspan=2>composite</td><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td rowspan=4>1xAIC0_RD_WR_L2_1xSDMA0_RD_WR_L2</td><td rowspan=4>composite</td><td>1xAIC0_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC0_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA0_RD_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA0_WR_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td rowspan=4>2xAIC_RD_L2_2xSDMA_RD_L2</td><td rowspan=4>composite</td><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td rowspan=4>2xAIC_WR_L2_2xSDMA_WR_L2</td><td rowspan=4>composite</td><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td rowspan=8>2xAIC_RD_RW_L2_2xSDMA_RD_WR_L2</td><td rowspan=8>composite</td><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td rowspan=8>2xAIC01_RD_RW_L2_2xSDMA01_RD_WR_L2</td><td rowspan=8>composite</td><td>1xAIC0_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC0_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA0_RD_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA0_WR_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC1_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC1_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA1_RD_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA1_WR_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td rowspan=8>4xAIC_RD_L2_4xSDMA_RD_L2</td><td rowspan=8>composite</td><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td rowspan=8>4xAIC_WR_L2_4xSDMA_WR_L2</td><td rowspan=8>composite</td><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td rowspan=16>4xAIC_RD_RW_L2_4xSDMA_RD_WR_L2</td><td rowspan=16>composite</td><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td rowspan=16>4xAIC0123_RD_RW_L2_4xSDMA0123_RD_WR_L2</td><td rowspan=16>composite</td><td>1xAIC0_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC0_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC1_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC1_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC2_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC2_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC3_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC3_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA0_RD_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA0_WR_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA1_RD_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA1_WR_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA2_RD_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA2_WR_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA3_RD_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA3_WR_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td rowspan=16>4xAIC4567_RD_RW_L2_4xSDMA0123_RD_WR_L2</td><td rowspan=16>composite</td><td>1xAIC4_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC4_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC5_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC5_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC6_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC6_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC7_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC7_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA0_RD_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA0_WR_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA1_RD_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA1_WR_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA2_RD_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA2_WR_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA3_RD_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA3_WR_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td rowspan=2>1xAIC_RD_DDRG_1xSDMA_RD_DDRG</td><td rowspan=2>composite</td><td>1xAIC_RD_DDRG</td><td>unit</td><td>aic</td><td>ddr_w</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_DDRG</td><td>unit</td><td>sdma</td><td>ddr_w</td><td>read</td><td>0.99</td></tr>
        <tr><td rowspan=2>1xAIC_WR_DDRG_1xSDMA_WR_DDRG</td><td rowspan=2>composite</td><td>1xAIC_WR_DDRG</td><td>unit</td><td>aic</td><td>ddr_w</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_DDRG</td><td>unit</td><td>sdma</td><td>ddr_w</td><td>write</td><td>0.99</td></tr>
        <tr><td rowspan=2>1xAIC_RD_DDRG_1xSDMA_WR_DDRG</td><td rowspan=2>composite</td><td>1xAIC_RD_DDRG</td><td>unit</td><td>aic</td><td>ddr_w</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_DDRG</td><td>unit</td><td>sdma</td><td>ddr_w</td><td>write</td><td>0.99</td></tr>
        <tr><td rowspan=2>1xAIC_WR_DDRG_1xSDMA_RD_DDRG</td><td rowspan=2>composite</td><td>1xAIC_WR_DDRG</td><td>unit</td><td>aic</td><td>ddr_w</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_DDRG</td><td>unit</td><td>sdma</td><td>ddr_w</td><td>read</td><td>0.99</td></tr>
        <tr><td rowspan=2>1xAIC_RD_DDRP_1xSDMA_RD_DDRP</td><td rowspan=2>composite</td><td>1xAIC_RD_DDRP</td><td>unit</td><td>aic</td><td>ddr_e</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_DDRP</td><td>unit</td><td>sdma</td><td>ddr_w</td><td>read</td><td>0.99</td></tr>
        <tr><td rowspan=2>1xAIC_WR_DDRP_1xSDMA_WR_DDRP</td><td rowspan=2>composite</td><td>1xAIC_WR_DDRP</td><td>unit</td><td>aic</td><td>ddr_e</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_DDRP</td><td>unit</td><td>sdma</td><td>ddr_w</td><td>write</td><td>0.99</td></tr>
        <tr><td rowspan=2>1xAIC_RD_DDRP_1xSDMA_WR_DDRP</td><td rowspan=2>composite</td><td>1xAIC_RD_DDRP</td><td>unit</td><td>aic</td><td>ddr_e</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_DDRP</td><td>unit</td><td>sdma</td><td>ddr_w</td><td>write</td><td>0.99</td></tr>
        <tr><td rowspan=2>1xAIC_WR_DDRP_1xSDMA_RD_DDRP</td><td rowspan=2>composite</td><td>1xAIC_WR_DDRP</td><td>unit</td><td>aic</td><td>ddr_e</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_DDRP</td><td>unit</td><td>sdma</td><td>ddr_w</td><td>read</td><td>0.99</td></tr>
        <tr><td rowspan=4>1xAIC_RD_DDRG_1xSDMA_RD_DDRG_1xAIC_RD_DDRP_1xSDMA_RD_DDRP</td><td rowspan=4>composite</td><td>1xAIC_RD_DDRG</td><td>unit</td><td>aic</td><td>ddr_w</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_DDRG</td><td>unit</td><td>sdma</td><td>ddr_w</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_DDRP</td><td>unit</td><td>aic</td><td>ddr_e</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_DDRP</td><td>unit</td><td>sdma</td><td>ddr_w</td><td>read</td><td>0.99</td></tr>
        <tr><td rowspan=4>1xAIC_WR_DDRG_1xSDMA_WR_DDRG_1xAIC_WR_DDRP_1xSDMA_WR_DDRP</td><td rowspan=4>composite</td><td>1xAIC_WR_DDRG</td><td>unit</td><td>aic</td><td>ddr_w</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_DDRG</td><td>unit</td><td>sdma</td><td>ddr_w</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_DDRP</td><td>unit</td><td>aic</td><td>ddr_e</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_DDRP</td><td>unit</td><td>sdma</td><td>ddr_w</td><td>write</td><td>0.99</td></tr>
        <tr><td rowspan=4>1xAIC_WR_DDRG_1xSDMA_WR_DDRG_1xAIC_RD_DDRP_1xSDMA_RD_DDRP</td><td rowspan=4>composite</td><td>1xAIC_WR_DDRG</td><td>unit</td><td>aic</td><td>ddr_w</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_DDRG</td><td>unit</td><td>sdma</td><td>ddr_w</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_DDRP</td><td>unit</td><td>aic</td><td>ddr_e</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_DDRP</td><td>unit</td><td>sdma</td><td>ddr_w</td><td>read</td><td>0.99</td></tr>
        <tr><td rowspan=4>1xAIC_RD_DDRG_1xSDMA_RD_DDRG_1xAIC_WR_DDRP_1xSDMA_WR_DDRP</td><td rowspan=4>composite</td><td>1xAIC_RD_DDRG</td><td>unit</td><td>aic</td><td>ddr_w</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_DDRG</td><td>unit</td><td>sdma</td><td>ddr_w</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_DDRP</td><td>unit</td><td>aic</td><td>ddr_e</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_DDRP</td><td>unit</td><td>sdma</td><td>ddr_w</td><td>write</td><td>0.99</td></tr>
        <tr><td rowspan=4>2xAIC_RD_DDRG_2xSDMA_RD_DDRP</td><td rowspan=4>composite</td><td>1xAIC_RD_DDRG</td><td>unit</td><td>aic</td><td>ddr_w</td><td>read</td><td>0.66</td></tr>
        <tr><td>1xAIC_RD_DDRG</td><td>unit</td><td>aic</td><td>ddr_w</td><td>read</td><td>0.66</td></tr>
        <tr><td>1xSDMA_RD_DDRP</td><td>unit</td><td>sdma</td><td>ddr_w</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_DDRP</td><td>unit</td><td>sdma</td><td>ddr_w</td><td>read</td><td>0.99</td></tr>
        <tr><td rowspan=4>2xAIC_RD_DDRP_2xSDMA_RD_DDRG</td><td rowspan=4>composite</td><td>1xAIC_RD_DDRP</td><td>unit</td><td>aic</td><td>ddr_e</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_DDRP</td><td>unit</td><td>aic</td><td>ddr_e</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_DDRG</td><td>unit</td><td>sdma</td><td>ddr_w</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_DDRG</td><td>unit</td><td>sdma</td><td>ddr_w</td><td>read</td><td>0.99</td></tr>
        <tr><td rowspan=4>2xAIC_WR_DDRG_2xSDMA_WR_DDRP</td><td rowspan=4>composite</td><td>1xAIC_WR_DDRG</td><td>unit</td><td>aic</td><td>ddr_w</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_DDRG</td><td>unit</td><td>aic</td><td>ddr_w</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_DDRP</td><td>unit</td><td>sdma</td><td>ddr_w</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_DDRP</td><td>unit</td><td>sdma</td><td>ddr_w</td><td>write</td><td>0.99</td></tr>
        <tr><td rowspan=4>2xAIC_WR_DDRP_2xSDMA_WR_DDRG</td><td rowspan=4>composite</td><td>1xAIC_WR_DDRP</td><td>unit</td><td>aic</td><td>ddr_e</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_DDRP</td><td>unit</td><td>aic</td><td>ddr_e</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_DDRG</td><td>unit</td><td>sdma</td><td>ddr_w</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_DDRG</td><td>unit</td><td>sdma</td><td>ddr_w</td><td>write</td><td>0.99</td></tr>
        <tr><td rowspan=4>2xAIC_RD_DDRG_2xSDMA_WR_DDRP</td><td rowspan=4>composite</td><td>1xAIC_RD_DDRG</td><td>unit</td><td>aic</td><td>ddr_w</td><td>read</td><td>0.66</td></tr>
        <tr><td>1xAIC_RD_DDRG</td><td>unit</td><td>aic</td><td>ddr_w</td><td>read</td><td>0.66</td></tr>
        <tr><td>1xSDMA_WR_DDRP</td><td>unit</td><td>sdma</td><td>ddr_w</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_DDRP</td><td>unit</td><td>sdma</td><td>ddr_w</td><td>write</td><td>0.99</td></tr>
        <tr><td rowspan=4>2xAIC_WR_DDRP_2xSDMA_RD_DDRG</td><td rowspan=4>composite</td><td>1xAIC_WR_DDRP</td><td>unit</td><td>aic</td><td>ddr_e</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_DDRP</td><td>unit</td><td>aic</td><td>ddr_e</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_DDRG</td><td>unit</td><td>sdma</td><td>ddr_w</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_DDRG</td><td>unit</td><td>sdma</td><td>ddr_w</td><td>read</td><td>0.99</td></tr>
        <tr><td rowspan=4>2xAIC_RD_DDRP_2xSDMA_WR_DDRG</td><td rowspan=4>composite</td><td>1xAIC_RD_DDRP</td><td>unit</td><td>aic</td><td>ddr_e</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_DDRP</td><td>unit</td><td>aic</td><td>ddr_e</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_DDRG</td><td>unit</td><td>sdma</td><td>ddr_w</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_DDRG</td><td>unit</td><td>sdma</td><td>ddr_w</td><td>write</td><td>0.99</td></tr>
        <tr><td rowspan=4>2xAIC_WR_DDRG_2xSDMA_RD_DDRP</td><td rowspan=4>composite</td><td>1xAIC_WR_DDRG</td><td>unit</td><td>aic</td><td>ddr_w</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_DDRG</td><td>unit</td><td>aic</td><td>ddr_w</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_DDRP</td><td>unit</td><td>sdma</td><td>ddr_w</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_DDRP</td><td>unit</td><td>sdma</td><td>ddr_w</td><td>read</td><td>0.99</td></tr>
        <tr><td rowspan=4>1xAIC_RD_L2_1xAIC_RD_DDRG_1xSDMA_RD_L2_1xSDMA_RD_DDRG</td><td rowspan=4>composite</td><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_DDRG</td><td>unit</td><td>aic</td><td>ddr_w</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_DDRG</td><td>unit</td><td>sdma</td><td>ddr_w</td><td>read</td><td>0.99</td></tr>
        <tr><td rowspan=4>1xAIC_WR_L2_1xAIC_WR_DDRG_1xSDMA_WR_L2_1xSDMA_WR_DDRG</td><td rowspan=4>composite</td><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_DDRG</td><td>unit</td><td>aic</td><td>ddr_w</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_DDRG</td><td>unit</td><td>sdma</td><td>ddr_w</td><td>write</td><td>0.99</td></tr>
        <tr><td rowspan=6>1xAIC_RD_WR_L2_1xAIC_RD_DDRG_1xSDMA_RD_WR_L2_1xSDMA_RD_DDRG</td><td rowspan=6>composite</td><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_DDRG</td><td>unit</td><td>aic</td><td>ddr_w</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_DDRG</td><td>unit</td><td>sdma</td><td>ddr_w</td><td>read</td><td>0.99</td></tr>
        <tr><td rowspan=6>1xAIC_RD_WR_L2_1xAIC_WR_DDRG_1xSDMA_RD_WR_L2_1xSDMA_WR_DDRG</td><td rowspan=6>composite</td><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_DDRG</td><td>unit</td><td>aic</td><td>ddr_w</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_DDRG</td><td>unit</td><td>sdma</td><td>ddr_w</td><td>write</td><td>0.99</td></tr>
        <tr><td rowspan=18>6xAIC_RD_WR_L2_1xAIC_RD_DDRG_2xSDMA_RD_WR_L2_2xSDMA_RD_DDRG</td><td rowspan=18>composite</td><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_DDRG</td><td>unit</td><td>sdma</td><td>ddr_w</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_DDRG</td><td>unit</td><td>sdma</td><td>ddr_w</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td rowspan=18>6xAIC_RD_WR_L2_1xAIC_RD_DDRG_2xSDMA_RD_WR_L2_2xSDMA_WR_DDRG</td><td rowspan=18>composite</td><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_DDRG</td><td>unit</td><td>sdma</td><td>ddr_w</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_DDRG</td><td>unit</td><td>sdma</td><td>ddr_w</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td rowspan=18>6xAIC_RD_L2_8xAIC_WR_L2_2xAIC_RD_DDRG_2xSDMA_RD_L2</td><td rowspan=18>composite</td><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_DDRG</td><td>unit</td><td>aic</td><td>ddr_w</td><td>read</td><td>0.66</td></tr>
        <tr><td>1xAIC_RD_DDRG</td><td>unit</td><td>aic</td><td>ddr_w</td><td>read</td><td>0.66</td></tr>
        <tr><td>1xSDMA_RD_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td rowspan=18>6xAIC_WR_L2_8xAIC_RD_L2_2xAIC_WR_DDRG_2xSDMA_WR_L2</td><td rowspan=18>composite</td><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_DDRG</td><td>unit</td><td>aic</td><td>ddr_w</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_DDRG</td><td>unit</td><td>aic</td><td>ddr_w</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td rowspan=4>1xAIC_RD_L2_1xAIC_RD_DDRP_1xSDMA_RD_L2_1xSDMA_RD_DDRP</td><td rowspan=4>composite</td><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_DDRP</td><td>unit</td><td>aic</td><td>ddr_e</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_DDRP</td><td>unit</td><td>sdma</td><td>ddr_w</td><td>read</td><td>0.99</td></tr>
        <tr><td rowspan=4>1xAIC_WR_L2_1xAIC_WR_DDRP_1xSDMA_WR_L2_1xSDMA_WR_DDRP</td><td rowspan=4>composite</td><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_DDRP</td><td>unit</td><td>aic</td><td>ddr_e</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_DDRP</td><td>unit</td><td>sdma</td><td>ddr_w</td><td>write</td><td>0.99</td></tr>
        <tr><td rowspan=6>1xAIC_RD_WR_L2_1xAIC_RD_DDRP_1xSDMA_RD_WR_L2_1xSDMA_RD_DDRP</td><td rowspan=6>composite</td><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_DDRP</td><td>unit</td><td>aic</td><td>ddr_e</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_DDRP</td><td>unit</td><td>sdma</td><td>ddr_w</td><td>read</td><td>0.99</td></tr>
        <tr><td rowspan=6>1xAIC_RD_WR_L2_1xAIC_WR_DDRP_1xSDMA_RD_WR_L2_1xSDMA_WR_DDRP</td><td rowspan=6>composite</td><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_DDRP</td><td>unit</td><td>aic</td><td>ddr_e</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_DDRP</td><td>unit</td><td>sdma</td><td>ddr_w</td><td>write</td><td>0.99</td></tr>
        <tr><td rowspan=18>6xAIC_RD_WR_L2_1xAIC_RD_DDRP_2xSDMA_RD_WR_L2_2xSDMA_RD_DDRP</td><td rowspan=18>composite</td><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_DDRP</td><td>unit</td><td>sdma</td><td>ddr_w</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_DDRP</td><td>unit</td><td>sdma</td><td>ddr_w</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td rowspan=18>6xAIC_RD_WR_L2_1xAIC_RD_DDRP_2xSDMA_RD_WR_L2_2xSDMA_WR_DDRP</td><td rowspan=18>composite</td><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_DDRP</td><td>unit</td><td>sdma</td><td>ddr_w</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_DDRP</td><td>unit</td><td>sdma</td><td>ddr_w</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td rowspan=18>6xAIC_RD_L2_8xAIC_WR_L2_2xAIC_RD_DDRP_2xSDMA_RD_L2</td><td rowspan=18>composite</td><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_DDRP</td><td>unit</td><td>aic</td><td>ddr_e</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_DDRP</td><td>unit</td><td>aic</td><td>ddr_e</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td rowspan=18>6xAIC_WR_L2_8xAIC_RD_L2_2xAIC_WR_DDRP_2xSDMA_WR_L2</td><td rowspan=18>composite</td><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_DDRP</td><td>unit</td><td>aic</td><td>ddr_e</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_DDRP</td><td>unit</td><td>aic</td><td>ddr_e</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td rowspan=20>4xAIC_RD_L2_8xAIC_WR_L2_4xSDMA_RD_L2_2xSDMA_WR_DDRG_2xSDMA_WR_DDRP</td><td rowspan=20>composite</td><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_DDRG</td><td>unit</td><td>sdma</td><td>ddr_w</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_DDRG</td><td>unit</td><td>sdma</td><td>ddr_w</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_DDRP</td><td>unit</td><td>sdma</td><td>ddr_w</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_DDRP</td><td>unit</td><td>sdma</td><td>ddr_w</td><td>write</td><td>0.99</td></tr>
        <tr><td rowspan=20>8xAIC_RD_L2_4xAIC_WR_L2_4xSDMA_WR_L2_2xSDMA_RD_DDRG_2xSDMA_RD_DDRP</td><td rowspan=20>composite</td><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_DDRG</td><td>unit</td><td>sdma</td><td>ddr_w</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_DDRG</td><td>unit</td><td>sdma</td><td>ddr_w</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_DDRP</td><td>unit</td><td>sdma</td><td>ddr_w</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_DDRP</td><td>unit</td><td>sdma</td><td>ddr_w</td><td>read</td><td>0.99</td></tr>
        <tr><td rowspan=16>4xAIC_RD_L2_4xAIC_WR_L2_4xSDMA_WR_L2_2xAIC_RD_DDRG_2xAIC_RD_DDRP</td><td rowspan=16>composite</td><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_DDRG</td><td>unit</td><td>aic</td><td>ddr_w</td><td>read</td><td>0.66</td></tr>
        <tr><td>1xAIC_RD_DDRG</td><td>unit</td><td>aic</td><td>ddr_w</td><td>read</td><td>0.66</td></tr>
        <tr><td>1xAIC_RD_DDRP</td><td>unit</td><td>aic</td><td>ddr_e</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_DDRP</td><td>unit</td><td>aic</td><td>ddr_e</td><td>read</td><td>0.99</td></tr>
        <tr><td rowspan=16>4xAIC_RD_L2_4xAIC_WR_L2_4xSDMA_RD_L2_2xAIC_WR_DDRG_2xAIC_WR_DDRP</td><td rowspan=16>composite</td><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_DDRG</td><td>unit</td><td>aic</td><td>ddr_w</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_DDRG</td><td>unit</td><td>aic</td><td>ddr_w</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_DDRP</td><td>unit</td><td>aic</td><td>ddr_e</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_DDRP</td><td>unit</td><td>aic</td><td>ddr_e</td><td>write</td><td>0.99</td></tr>
        <tr><td rowspan=20>6xAIC_RD_L2_6xAIC_WR_L2_2xSDMA_RD_L2_2xSDMA_WR_L2_2xSDMA_RD_DDRP_2xSDMA_WR_DDRG</td><td rowspan=20>composite</td><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_DDRP</td><td>unit</td><td>sdma</td><td>ddr_w</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_DDRP</td><td>unit</td><td>sdma</td><td>ddr_w</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_DDRG</td><td>unit</td><td>sdma</td><td>ddr_w</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_DDRG</td><td>unit</td><td>sdma</td><td>ddr_w</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td rowspan=20>6xAIC_RD_L2_6xAIC_WR_L2_2xSDMA_RD_L2_2xSDMA_WR_L2_2xSDMA_RD_DDRG_2xSDMA_WR_DDRP</td><td rowspan=20>composite</td><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_DDRG</td><td>unit</td><td>sdma</td><td>ddr_w</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_DDRG</td><td>unit</td><td>sdma</td><td>ddr_w</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_DDRP</td><td>unit</td><td>sdma</td><td>ddr_w</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_DDRP</td><td>unit</td><td>sdma</td><td>ddr_w</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td rowspan=2>1xPVE_RD_L2_1xDEC_RD_L2</td><td rowspan=2>composite</td><td>1xPVE_RD_L2</td><td>unit</td><td>pve</td><td>l2</td><td>read</td><td>0.75</td></tr>
        <tr><td>1xDEC_RD_L2</td><td>unit</td><td>dec</td><td>l2</td><td>read</td><td>0.75</td></tr>
        <tr><td rowspan=2>1xPVE_WR_L2_1xDEC_WR_L2</td><td rowspan=2>composite</td><td>1xPVE_WR_L2</td><td>unit</td><td>pve</td><td>l2</td><td>write</td><td>0.75</td></tr>
        <tr><td>1xDEC_WR_L2</td><td>unit</td><td>dec</td><td>l2</td><td>write</td><td>0.75</td></tr>
        <tr><td rowspan=4>1xPVE_RD_WR_L2_1xDEC_RD_WR_L2</td><td rowspan=4>composite</td><td>1xPVE_RD_L2</td><td>unit</td><td>pve</td><td>l2</td><td>read</td><td>0.75</td></tr>
        <tr><td>1xPVE_WR_L2</td><td>unit</td><td>pve</td><td>l2</td><td>write</td><td>0.75</td></tr>
        <tr><td>1xDEC_RD_L2</td><td>unit</td><td>dec</td><td>l2</td><td>read</td><td>0.75</td></tr>
        <tr><td>1xDEC_WR_L2</td><td>unit</td><td>dec</td><td>l2</td><td>write</td><td>0.75</td></tr>
        <tr><td rowspan=2>1xPVE_RD_DDRP_1xDEC_RD_DDRP</td><td rowspan=2>composite</td><td>1xPVE_RD_DDRP</td><td>unit</td><td>pve</td><td>ddr_e</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xDEC_RD_DDRP</td><td>unit</td><td>dec</td><td>ddr_e</td><td>read</td><td>0.99</td></tr>
        <tr><td rowspan=2>1xPVE_WR_DDRP_1xDEC_WR_DDRP</td><td rowspan=2>composite</td><td>1xPVE_WR_DDRP</td><td>unit</td><td>pve</td><td>ddr_e</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xDEC_WR_DDRP</td><td>unit</td><td>dec</td><td>ddr_e</td><td>write</td><td>0.99</td></tr>
        <tr><td rowspan=3>2xPVE_RD_DDRP_1xDEC_RD_DDRP</td><td rowspan=3>composite</td><td>1xPVE_RD_DDRP</td><td>unit</td><td>pve</td><td>ddr_e</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xPVE_RD_DDRP</td><td>unit</td><td>pve</td><td>ddr_e</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xDEC_RD_DDRP</td><td>unit</td><td>dec</td><td>ddr_e</td><td>read</td><td>0.99</td></tr>
        <tr><td rowspan=3>2xPVE_WR_DDRP_1xDEC_WR_DDRP</td><td rowspan=3>composite</td><td>1xPVE_WR_DDRP</td><td>unit</td><td>pve</td><td>ddr_e</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xPVE_WR_DDRP</td><td>unit</td><td>pve</td><td>ddr_e</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xDEC_WR_DDRP</td><td>unit</td><td>dec</td><td>ddr_e</td><td>write</td><td>0.99</td></tr>
        <tr><td rowspan=3>1xPVE_RD_DDRP_2xDEC_RD_DDRP</td><td rowspan=3>composite</td><td>1xPVE_RD_DDRP</td><td>unit</td><td>pve</td><td>ddr_e</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xDEC_RD_DDRP</td><td>unit</td><td>dec</td><td>ddr_e</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xDEC_RD_DDRP</td><td>unit</td><td>dec</td><td>ddr_e</td><td>read</td><td>0.99</td></tr>
        <tr><td rowspan=3>1xPVE_WR_DDRP_2xDEC_WR_DDRP</td><td rowspan=3>composite</td><td>1xPVE_WR_DDRP</td><td>unit</td><td>pve</td><td>ddr_e</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xDEC_WR_DDRP</td><td>unit</td><td>dec</td><td>ddr_e</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xDEC_WR_DDRP</td><td>unit</td><td>dec</td><td>ddr_e</td><td>write</td><td>0.99</td></tr>
        <tr><td rowspan=4>2xPVE_RD_DDRP_2xDEC_RD_DDRP</td><td rowspan=4>composite</td><td>1xPVE_RD_DDRP</td><td>unit</td><td>pve</td><td>ddr_e</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xPVE_RD_DDRP</td><td>unit</td><td>pve</td><td>ddr_e</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xDEC_RD_DDRP</td><td>unit</td><td>dec</td><td>ddr_e</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xDEC_RD_DDRP</td><td>unit</td><td>dec</td><td>ddr_e</td><td>read</td><td>0.99</td></tr>
        <tr><td rowspan=4>2xPVE_WR_DDRP_2xDEC_WR_DDRP</td><td rowspan=4>composite</td><td>1xPVE_WR_DDRP</td><td>unit</td><td>pve</td><td>ddr_e</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xPVE_WR_DDRP</td><td>unit</td><td>pve</td><td>ddr_e</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xDEC_WR_DDRP</td><td>unit</td><td>dec</td><td>ddr_e</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xDEC_WR_DDRP</td><td>unit</td><td>dec</td><td>ddr_e</td><td>write</td><td>0.99</td></tr>
        <tr><td rowspan=3>1xPVE_RD_DDRP_1xDEC_RD_DDRP_1xPCIE_RD_DDRP</td><td rowspan=3>composite</td><td>1xPVE_RD_DDRP</td><td>unit</td><td>pve</td><td>ddr_e</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xDEC_RD_DDRP</td><td>unit</td><td>dec</td><td>ddr_e</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xPCIE_RD_DDRP</td><td>unit</td><td>pcie</td><td>ddr_e</td><td>read</td><td>0.99</td></tr>
        <tr><td rowspan=3>1xPVE_WR_DDRP_1xDEC_WR_DDRP_1xPCIE_WR_DDRP</td><td rowspan=3>composite</td><td>1xPVE_WR_DDRP</td><td>unit</td><td>pve</td><td>ddr_e</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xDEC_WR_DDRP</td><td>unit</td><td>dec</td><td>ddr_e</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xPCIE_WR_DDRP</td><td>unit</td><td>pcie</td><td>ddr_e</td><td>write</td><td>0.99</td></tr>
        <tr><td rowspan=4>1xPVE_RD_DDRP_2xDEC_RD_DDRP_1xPCIE_RD_DDRP</td><td rowspan=4>composite</td><td>1xPVE_RD_DDRP</td><td>unit</td><td>pve</td><td>ddr_e</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xDEC_RD_DDRP</td><td>unit</td><td>dec</td><td>ddr_e</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xDEC_RD_DDRP</td><td>unit</td><td>dec</td><td>ddr_e</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xPCIE_RD_DDRP</td><td>unit</td><td>pcie</td><td>ddr_e</td><td>read</td><td>0.99</td></tr>
        <tr><td rowspan=4>1xPVE_WR_DDRP_2xDEC_WR_DDRP_1xPCIE_WR_DDRP</td><td rowspan=4>composite</td><td>1xPVE_WR_DDRP</td><td>unit</td><td>pve</td><td>ddr_e</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xDEC_WR_DDRP</td><td>unit</td><td>dec</td><td>ddr_e</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xDEC_WR_DDRP</td><td>unit</td><td>dec</td><td>ddr_e</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xPCIE_WR_DDRP</td><td>unit</td><td>pcie</td><td>ddr_e</td><td>write</td><td>0.99</td></tr>
        <tr><td rowspan=4>2xPVE_RD_DDRP_1xDEC_RD_DDRP_1xPCIE_RD_DDRP</td><td rowspan=4>composite</td><td>1xPVE_RD_DDRP</td><td>unit</td><td>pve</td><td>ddr_e</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xPVE_RD_DDRP</td><td>unit</td><td>pve</td><td>ddr_e</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xDEC_RD_DDRP</td><td>unit</td><td>dec</td><td>ddr_e</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xPCIE_RD_DDRP</td><td>unit</td><td>pcie</td><td>ddr_e</td><td>read</td><td>0.99</td></tr>
        <tr><td rowspan=4>2xPVE_WR_DDRP_1xDEC_WR_DDRP_1xPCIE_WR_DDRP</td><td rowspan=4>composite</td><td>1xPVE_WR_DDRP</td><td>unit</td><td>pve</td><td>ddr_e</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xPVE_WR_DDRP</td><td>unit</td><td>pve</td><td>ddr_e</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xDEC_WR_DDRP</td><td>unit</td><td>dec</td><td>ddr_e</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xPCIE_WR_DDRP</td><td>unit</td><td>pcie</td><td>ddr_e</td><td>write</td><td>0.99</td></tr>
        <tr><td rowspan=5>2xPVE_RD_DDRP_2xDEC_RD_DDRP_1xPCIE_RD_DDRP</td><td rowspan=5>composite</td><td>1xPVE_RD_DDRP</td><td>unit</td><td>pve</td><td>ddr_e</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xPVE_RD_DDRP</td><td>unit</td><td>pve</td><td>ddr_e</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xDEC_RD_DDRP</td><td>unit</td><td>dec</td><td>ddr_e</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xDEC_RD_DDRP</td><td>unit</td><td>dec</td><td>ddr_e</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xPCIE_RD_DDRP</td><td>unit</td><td>pcie</td><td>ddr_e</td><td>read</td><td>0.99</td></tr>
        <tr><td rowspan=5>2xPVE_WR_DDRP_2xDEC_WR_DDRP_1xPCIE_WR_DDRP</td><td rowspan=5>composite</td><td>1xPVE_WR_DDRP</td><td>unit</td><td>pve</td><td>ddr_e</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xPVE_WR_DDRP</td><td>unit</td><td>pve</td><td>ddr_e</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xDEC_WR_DDRP</td><td>unit</td><td>dec</td><td>ddr_e</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xDEC_WR_DDRP</td><td>unit</td><td>dec</td><td>ddr_e</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xPCIE_WR_DDRP</td><td>unit</td><td>pcie</td><td>ddr_e</td><td>write</td><td>0.99</td></tr>
        <tr><td rowspan=3>1xAIC_RD_L2_1xSDMA_RD_L2_1xPVE_RD_L2</td><td rowspan=3>composite</td><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xPVE_RD_L2</td><td>unit</td><td>pve</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td rowspan=3>1xAIC_WR_L2_1xSDMA_WR_L2_1xPVE_WR_L2</td><td rowspan=3>composite</td><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xPVE_WR_L2</td><td>unit</td><td>pve</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td rowspan=6>1xAIC_RD_WR_L2_1xSDMA_RD_WR_L2_1xPVE_RD_WR_L2</td><td rowspan=6>composite</td><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xPVE_RD_L2</td><td>unit</td><td>pve</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xPVE_WR_L2</td><td>unit</td><td>pve</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td rowspan=16>3xAIC_RD_WR_L2_4xSDMA_RD_WR_L2_1xPVE_RD_WR_L2</td><td rowspan=16>composite</td><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xPVE_RD_L2</td><td>unit</td><td>pve</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xPVE_WR_L2</td><td>unit</td><td>pve</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td rowspan=3>1xAIC_RD_DDRG_1xSDMA_RD_DDRG_1xPVE_RD_DDRG</td><td rowspan=3>composite</td><td>1xAIC_RD_DDRG</td><td>unit</td><td>aic</td><td>ddr_w</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_DDRG</td><td>unit</td><td>sdma</td><td>ddr_w</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xPVE_RD_DDRG</td><td>unit</td><td>pve</td><td>ddr_w</td><td>read</td><td>0.99</td></tr>
        <tr><td rowspan=3>1xAIC_WR_DDRG_1xSDMA_WR_DDRG_1xPVE_WR_DDRG</td><td rowspan=3>composite</td><td>1xAIC_WR_DDRG</td><td>unit</td><td>aic</td><td>ddr_w</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_DDRG</td><td>unit</td><td>sdma</td><td>ddr_w</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xPVE_WR_DDRG</td><td>unit</td><td>pve</td><td>ddr_w</td><td>write</td><td>0.99</td></tr>
        <tr><td rowspan=3>1xAIC_RD_DDRP_1xSDMA_RD_DDRP_1xPVE_RD_DDRP</td><td rowspan=3>composite</td><td>1xAIC_RD_DDRP</td><td>unit</td><td>aic</td><td>ddr_e</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_DDRP</td><td>unit</td><td>sdma</td><td>ddr_w</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xPVE_RD_DDRP</td><td>unit</td><td>pve</td><td>ddr_e</td><td>read</td><td>0.99</td></tr>
        <tr><td rowspan=3>1xAIC_WR_DDRP_1xSDMA_WR_DDRP_1xPVE_WR_DDRP</td><td rowspan=3>composite</td><td>1xAIC_WR_DDRP</td><td>unit</td><td>aic</td><td>ddr_e</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_DDRP</td><td>unit</td><td>sdma</td><td>ddr_w</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xPVE_WR_DDRP</td><td>unit</td><td>pve</td><td>ddr_e</td><td>write</td><td>0.99</td></tr>
        <tr><td rowspan=4>1xAIC_RD_DDRG_1xPVE_RD_DDRG_1xAIC_RD_DDRP_1xPVE_RD_DDRP</td><td rowspan=4>composite</td><td>1xAIC_RD_DDRG</td><td>unit</td><td>aic</td><td>ddr_w</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xPVE_RD_DDRG</td><td>unit</td><td>pve</td><td>ddr_w</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_DDRP</td><td>unit</td><td>aic</td><td>ddr_e</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xPVE_RD_DDRP</td><td>unit</td><td>pve</td><td>ddr_e</td><td>read</td><td>0.99</td></tr>
        <tr><td rowspan=4>1xAIC_WR_DDRG_1xPVE_WR_DDRG_1xAIC_WR_DDRP_1xPVE_WR_DDRP</td><td rowspan=4>composite</td><td>1xAIC_WR_DDRG</td><td>unit</td><td>aic</td><td>ddr_w</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xPVE_WR_DDRG</td><td>unit</td><td>pve</td><td>ddr_w</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_DDRP</td><td>unit</td><td>aic</td><td>ddr_e</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xPVE_WR_DDRP</td><td>unit</td><td>pve</td><td>ddr_e</td><td>write</td><td>0.99</td></tr>
        <tr><td rowspan=18>8xAIC_RD_WR_L2_2xPVE_RD_DDRP</td><td rowspan=18>composite</td><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xPVE_RD_DDRP</td><td>unit</td><td>pve</td><td>ddr_e</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xPVE_RD_DDRP</td><td>unit</td><td>pve</td><td>ddr_e</td><td>read</td><td>0.99</td></tr>
        <tr><td rowspan=20>8xAIC_RD_L2_6xAIC_WR_L2_2xSDMA_WR_L2_2xSDMA_RD_DDRG_2xPVE_RD_DDRP</td><td rowspan=20>composite</td><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_DDRG</td><td>unit</td><td>sdma</td><td>ddr_w</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_DDRG</td><td>unit</td><td>sdma</td><td>ddr_w</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xPVE_RD_DDRP</td><td>unit</td><td>pve</td><td>ddr_e</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xPVE_RD_DDRP</td><td>unit</td><td>pve</td><td>ddr_e</td><td>read</td><td>0.99</td></tr>
        <tr><td rowspan=20>8xAIC_WR_L2_6xAIC_RD_L2_2xSDMA_RD_L2_2xSDMA_WR_DDRG_2xPVE_WR_DDRP</td><td rowspan=20>composite</td><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_RD_L2</td><td>unit</td><td>aic</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xAIC_WR_L2</td><td>unit</td><td>aic</td><td>l2</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_RD_L2</td><td>unit</td><td>sdma</td><td>l2</td><td>read</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_DDRG</td><td>unit</td><td>sdma</td><td>ddr_w</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xSDMA_WR_DDRG</td><td>unit</td><td>sdma</td><td>ddr_w</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xPVE_WR_DDRP</td><td>unit</td><td>pve</td><td>ddr_e</td><td>write</td><td>0.99</td></tr>
        <tr><td>1xPVE_WR_DDRP</td><td>unit</td><td>pve</td><td>ddr_e</td><td>write</td><td>0.99</td></tr>
    </tbody>
</table>





