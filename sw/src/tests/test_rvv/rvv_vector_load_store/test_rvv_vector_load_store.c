// Description: This test application demonstrates the utilization of RISC-V vector extension instructions
// for performing various vector load and store operations on a data array. It showcases operations such
// as vector element load and store, segment load and store, and handling of non-aligned memory accesses
// with different segment widths (SEW). These tests are executed across multiple scalar element widths
// (SEW 8, 16, 32) to verify the vector instruction's functionality under various data alignment and size
// conditions.

#include <riscv_vector.h>

static uint32_t __attribute__((aligned(64), section(".l1"))) data_u32[] = {
    0xeef90126, 0xe8089c73, 0x3aaf651e, 0x7984513b, 0xd1184828, 0x6d116053, 0xbdb5b172, 0x3c339e8b,  //
    0x713bce68, 0x75e28834, 0xe04e93af, 0xe47a267e, 0xe7245005, 0xdbe40f25, 0xe7462569, 0xbc879f2e,  //
    0x90911f11, 0xc357cf72, 0xe337521e, 0x03ae0c93, 0x8a54d0e4, 0xbf480b13, 0x5e21fbd6, 0x49dc1d4d,  //
    0xe82b0c93, 0x8382e36d, 0xfd6070f4, 0x7508f200, 0xc7be5827, 0x26f7cf89, 0xdb146ee2, 0x3126861f,  //
    0x765baaa1, 0x84062062, 0xecb2d13c, 0x49588812, 0x85e15503, 0x519ae42f, 0xf94bc552, 0x822fd872,  //
    0xea103a09, 0xfe58e458, 0x23f843cd, 0xc07c4805, 0x9f83fbe8, 0xbfd3d3b3, 0xaa50bc93, 0x5fb61dd1,  //
    0x052257be, 0x00d3596d, 0x3369594b, 0x13fbe040, 0x963295f9, 0xdacbcefc, 0x20a49b20, 0x867a52cc,  //
    0x9c1ddc45, 0x34d317d5, 0x5c8d41ae, 0x422002cf, 0xaa7a71d0, 0x942ca726, 0x2778e3ca, 0x88e7b804,  //
    0xae2ea0c3, 0x958a3117, 0x25bdaf1f, 0x1470ce72, 0x121192c5, 0x8a1ca2f2, 0x13fd61ff, 0x9d6abc63,  //
    0x7baf5320, 0xc50c277e, 0xbb11f773, 0xd5fccf17, 0x3726b685, 0xa0a4062c, 0x1e86e088, 0xe1484442,  //
    0x3d99685e, 0xfc1d63b8, 0xa67167a5, 0x4a6851be, 0x5c172e2b, 0x2126cb3e, 0x99e9cecc, 0x00ccf012,  //
    0x26fff6ae, 0xd197b225, 0xc8a8a846, 0x7cde0842, 0x20399dc1, 0xcc8683ee, 0x5fe59ffa, 0x73a54907,  //
    0xdf4cd611, 0x1c2003e3, 0x3bc6d545, 0x890ee922, 0x71dfd124, 0x3a3105fc, 0xce6f572c, 0x2c39b541,  //
    0x4f41acb5, 0x78a7399c, 0x2e47fd30, 0x4626df69, 0xbd2762c9, 0xf0f44440, 0xa98c68df, 0x80b920c9,  //
    0xb0af3410, 0xbe2572e7, 0xc0fb7fe6, 0x1e70cc20, 0x9ea5a2a7, 0xcb298ca7, 0xdf17dd21, 0x8433ac6d,  //
    0xb3bb9728, 0xc71fa972, 0xd19cfc36, 0x96b08204, 0xc6c26423, 0xc506dac9, 0xedfd6e03, 0x06a47f36,  //
    0x7ccf38a6, 0x68732be2, 0x9c7f687c, 0xe1724a14, 0xc50793bb, 0x4b4d1acc, 0x3717cdc0, 0xafaceee3,  //
    0xffce6d5b, 0x12626e6b, 0x7fd19fd7, 0x00775a70, 0x07394e28, 0xd41309d6, 0xef066afa, 0x6313cbf2,  //
    0x8d0be4a7, 0x011def92, 0x79f7e5e9, 0x86eb55d7, 0xf28fdbaf, 0x3d04c44d, 0x001a8a01, 0x8f151603,  //
    0x3ed894c4, 0x72f9a62f, 0x4c64711c, 0xd03878de, 0xfc5b70a9, 0x89c7acea, 0x9cb63e87, 0xa34fea0a,  //
    0x5aae09f7, 0x3632d92c, 0xca2a68c3, 0x07be7ae3, 0x5ea1ea3c, 0x6fbb8346, 0x6537cae1, 0x7bbc3e5f,  //
    0xab5609ae, 0x9a91bace, 0x634e3cf0, 0x18abf898, 0x1bcaf28d, 0xad46ca8c, 0x9c7074ef, 0x5d071bf5,  //
    0xb915c09f, 0x4db16e52, 0xa17a39cf, 0x18c44021, 0x6597c033, 0x649562aa, 0x9d0902f1, 0x8b1f2027,  //
    0xc111246b, 0x28313dfc, 0xab0d6e95, 0xcd6f973f, 0x57011e73, 0xcb262ff1, 0x6a10f34f, 0x84a06fa4,  //
    0xa749cbe4, 0xbc278860, 0x154127aa, 0x718a0ba5, 0xd0242af0, 0x3efbd376, 0x242b698e, 0x65335bf4,  //
    0xac99e305, 0xb71e773e, 0xc3c2977c, 0xcd5fe9b0, 0xe3028bd6, 0xa3230f5b, 0x44134a79, 0xfa5c6f9a,  //
    0x92d2adcf, 0x6758feb8, 0xb2c4ee54, 0x3be20ec4, 0x84945349, 0xa35ad8fd, 0x0f1a6ddb, 0x4cddae17,  //
    0x59b6d9ab, 0x2fa524dc, 0x6d58e10d, 0x342638b8, 0x6f357524, 0xffaceb82, 0xaad6cb44, 0x9c39c5e0,  //
    0x6a6f171d, 0xc45470e8, 0x2199c5df, 0x59b0ded8, 0xce550b70, 0xe66043d3, 0x867d040c, 0x74176d8c,  //
    0x849e345a, 0x69750605, 0x5d03e60d, 0xaa152db4, 0x459a5dc2, 0xd161fede, 0x20ca1209, 0x7d6c84cd,  //
    0xa832104e, 0x6e37fe6f, 0xeec374a8, 0xad203e02, 0x1c9815f4, 0x6cb7ef44, 0x30938986, 0x95a3b4cd,  //
    0x414022d3, 0x0e36fd11, 0x6e740444, 0x60dbbc50, 0x5dfedfa7, 0xecbf7f83, 0x791f8e1c, 0x1925cdfd,  //
    0x813e79d4, 0x0a8658e7, 0x6211f9f5, 0xca02c557, 0xfd77c6ea, 0x3e658652, 0xc1ef406d, 0x1588af2c,  //
    0xf9f02c19, 0x4b3cc2e1, 0x4d193570, 0x6e6aa527, 0x12b09872, 0xcd69dcdc, 0x96436dc1, 0x175a1db9,  //
    0x80ca84e7, 0x5ca2cd1c, 0x428b3b55, 0x30bf57d9, 0x50b40e4a, 0xabaf78c4, 0xb0703791, 0x9342d435,  //
    0xe952e29d, 0xf26ffea9, 0x591967ad, 0xffcf2dc0, 0x87efffbe, 0x1785db26, 0x6875dfab, 0x243b67f2,  //
    0xd06cbf75, 0xaaf2f04d, 0x27ab7b3c, 0x5e6789d0, 0x651f2e80, 0x666ad59d, 0x476fe215, 0x928a04a9,  //
    0xe1765d0a, 0xd58469bc, 0xa48f4891, 0x7738201d, 0xa43cd8ac, 0x2e4ece84, 0x45e42abf, 0xf2c288c6,  //
    0xa920f86c, 0xdb9ea235, 0x8857ab4b, 0xe1023a18, 0x7c6ea111, 0xbc05817f, 0xb84ca813, 0xf2e1a904,  //
    0x33e7b454, 0x2147af0a, 0x61cc95d9, 0x0142a139, 0x64de8dc6, 0xce2999f7, 0x76982af9, 0xc59d39f6,  //
    0xd4d37cf9, 0x9d3e52ae, 0x2768b20f, 0x29358599, 0xd423f02c, 0x4aa457a1, 0x6c4c632c, 0xe8f6ccab,  //
    0xc0a9fbd9, 0x7efe6ae3, 0x13bd8473, 0xcae4d303, 0xdef6e428, 0x70b165de, 0xb58a5845, 0x5a234aa9,  //
    0x075d9ca5, 0x8c94e781, 0xa892dc77, 0x919c6e26, 0xa768d7ca, 0xf32dea83, 0x07367774, 0x74775ce4,  //
    0xe01b857f, 0x7dc8c1fa, 0x7825e7c1, 0x162eea2f, 0xb7b598a3, 0x957dfa22, 0x76dd216c, 0x2338e57e,  //
    0x736ee6b5, 0x33e62e0c, 0x36c18b21, 0x70b6df5b, 0x871af8a3, 0xa958042a, 0x2387cee5, 0xc1cbb8f9,  //
    0xdc2432e6, 0x3c85e51d, 0x729355b3, 0x52ced51d, 0x9902a0c2, 0xf7fc6d55, 0x0a0dae2e, 0xd6b67421,  //
    0x6aa2964d, 0x02b86805, 0x074f8415, 0x8c705a4f, 0xe9b81f1f, 0xe19ae7cf, 0x3793624a, 0xc24c08c5,  //
    0x8b65241f, 0xd8c7ef8b, 0x0fa888f7, 0x365ea547, 0x0cfe870f, 0x9b57aa81, 0x4b83af34, 0x132487ef,  //
    0x7bff3e0b, 0xce1b3b2f, 0x54f6be4f, 0xc23b074e, 0x63d0a5eb, 0xda7c094a, 0x1fd81d28, 0x4dada154,  //
    0x72f06699, 0x6d722ef9, 0xec30166c, 0x60ed1846, 0x87ce8db6, 0x87924fa2, 0x385d9b41, 0x79563e31,  //
    0x76bdbe28, 0xa8f4453b, 0x33ed42f6, 0xb1b40ba5, 0xb1e4d551, 0xff0ff3d5, 0xc0d3b205, 0x48212dd9,  //
    0x8337be3f, 0x2b60277c, 0xc8d80cc8, 0xa3969d28, 0xa3b18b23, 0xb65817c4, 0xafbb2708, 0x461668ca,  //
    0x1e06dd0e, 0xc99ed7fa, 0x6350129e, 0x2b0f1d8a, 0x419c9f80, 0x506a0c51, 0xf99b63e8, 0xb5312865,  //
    0xad530bc3, 0x65e87643, 0xb3c5d627, 0xfdbd4a76, 0xa05129d1, 0xfb86777a, 0xc52fc5f6, 0x64f96e10,  //
    0xf022925b, 0xa58249c2, 0xd9c1d8e6, 0x3797343b, 0xc3fc62a7, 0x02c46c67, 0x870da6ee, 0xa685fd1c,  //
    0x143a8677, 0xed4d29a1, 0xd7f275f5, 0xd3acb8dd, 0xcaf81b8f, 0xb22e3c82, 0x31643964, 0xaec26c8e,  //
    0x4eabfecb, 0x109bfa51, 0xdc561cc3, 0xd18a0cdb, 0x617f499a, 0xfb825be6, 0xe2b9b51f, 0x8c28e5a6,  //
    0xe74e164c, 0x6a258c90, 0x09338726, 0x8a8e6412, 0xe9c2250d, 0x08492aa2, 0x398618eb, 0x64f31420,  //
    0x1a0c7792, 0xf3700e0f, 0xeebbddc9, 0x18044982, 0xcb06c587, 0xca5b668a, 0x2f110a4b, 0xdd769213,  //
    0x69971bea, 0x6c4e1b44, 0x4f4cae9b, 0xeeb74dd9, 0xbe453b86, 0x3256b636, 0x8514e816, 0x221c6e4a,  //
    0x89786632, 0x3c6da728, 0xa171cc30, 0xe4cddec7, 0x1f8de8f3, 0xa38fe8be, 0xc12a4dd6, 0x9cdbd1d9,  //
    0x11e21011, 0x01ad22b4, 0x57c53516, 0x3b678a36, 0x1d7fe2b4, 0x957f2c48, 0xafe5e4db, 0xa4a847f1,  //
    0x6756c7dc, 0xd14db787, 0xf40966af, 0x2bdb9bbf, 0x67f779af, 0x74d0a24d, 0xc40b7619, 0xd5d31233,  //
    0x88ec2da5, 0xd2b3f16e, 0x6f66d4b2, 0x1332c4c3, 0xfbcd1387, 0x128944c8, 0xc8eee514, 0xc79237f0,  //
    0x9d48f891, 0x7d140704, 0x7f58dc6e, 0xe58ce35b, 0xb82357e4, 0x6697e830, 0x32c7607b, 0xb981417c,  //
    0x3793ef69, 0x23ee6af6, 0xa2299621, 0xc9247f1d, 0x56704e68, 0xdd692cd0, 0xed495736, 0x4db6080e,  //
    0x8ae2173d, 0x27aec751, 0xdad83d3c, 0x9b76fa62, 0x6e314554, 0x1f0132a8, 0x1115eeaa, 0x9b5b062e,  //
    0xdeb0f053, 0x795ba386, 0x37783bd3, 0x48f24727, 0x6b195250, 0x4480f059, 0x39ca7089, 0x6ba3199d,  //
    0xd61fb5c2, 0x00059173, 0x81517ec9, 0x1044c4ed, 0x848430e3, 0x1bc3efd5, 0xe20d5a32, 0x43f8c648,  //
    0xfff14cab, 0x94f0574e, 0x71c695aa, 0x4ab42e63, 0x48ef1cf1, 0x728933ce, 0x02376955, 0xda7e29b3,  //
    0xce87fdf1, 0x49896804, 0x627bdb6b, 0xba54d254, 0x39947e8a, 0x00c1e8a4, 0xe687471c, 0xbe26516e,  //
    0x0ecd7068, 0x1e6fe45b, 0x7c9509b8, 0x8c2317aa, 0x5ce10e9a, 0xc540c34f, 0x89c72fbe, 0x76883c9b,  //
    0x33fb5a4d, 0xbb00dcc4, 0xe09a06a3, 0x5679f183, 0x50ac3f23, 0xe0aefd5d, 0x6b2c0ccb, 0x0adbd3a6,  //
    0x76cbf6c1, 0x4ba2bf88, 0x239e03cc, 0x0109ee84, 0x1bfe09ac, 0x754ffd77, 0x2e040863, 0x4f7fc004,  //
    0x85ab43fa, 0x243dd084, 0x4fb73ac2, 0x3dc40d42, 0x44a6246c, 0x9ce79f99, 0xa1de898e, 0x9225f6fb,  //
    0xbc080907, 0xe0baa2d6, 0x3dbe3b19, 0xd0e50830, 0xe1157b80, 0x0d51f889, 0xc882c9d2, 0x1b654bf1,  //
    0xb72e0cb3, 0xc9be637f, 0x58f97ebc, 0x6baa6c92, 0x868e8222, 0xe12c2718, 0x70109e63, 0xb8a71e24,  //
    0x56f04368, 0x8250155b, 0xf15e5987, 0x3f1811dd, 0x286c326c, 0x43b6a224, 0xa27dffcd, 0xab475a0c,  //
    0x3f6fdaae, 0xb2684ceb, 0x5cfb8041, 0x125281f2, 0xa22cbb1c, 0x0dbd662b, 0xa3e2f9b7, 0x188f23d1,  //
    0xce4d0d7c, 0x3f9b30b3, 0x70968678, 0xfa12f958, 0x7df2e864, 0x278bca40, 0x7a01daf8, 0x7e91b2d8,  //
    0x2cf72e00, 0x29474be1, 0x5deea28d, 0x4337908d, 0x86522716, 0xb25175d7, 0xd33e323f, 0x995b60b2,  //
    0xcc3c62cd, 0x21d5238d, 0xfae31f65, 0x9dedc271, 0x1c5afcd4, 0x984a1d17, 0x17e67797, 0xbd1dd863,  //
    0xe5873fbb, 0x33241b7d, 0x35d353a8, 0x1785b286, 0xfa04275c, 0xec7bd9a1, 0x54b21d3f, 0x5ba042f8,  //
    0x72fa2595, 0x52eec72f, 0x99ab221d, 0xe813e3b2, 0x268aa484, 0xc0d57c75, 0x692ba827, 0x00cf83c4,  //
    0xe08993d3, 0x26c2e438, 0x125cf563, 0x274c6d43, 0x9e183c25, 0xc7dba911, 0x7e75d5e3, 0x86114b81,  //
    0x4ba9acb9, 0x1500bf94, 0x499638b6, 0x27004554, 0x5271f08d, 0x30976b1b, 0x8f3f37e3, 0xa04b3ea9,  //
    0x0323933c, 0x791f587f, 0x1d7bda36, 0x61512c44, 0x4dda83bf, 0x9e050d36, 0xc8fdc4a5, 0x07c9b011,  //
    0xa7760c81, 0x5fc9d2fa, 0xad7dd5cd, 0x414e379b, 0x82554ddd, 0x84553ad5, 0xeb2d91c5, 0x0a829bdd,  //
    0x31e8b9af, 0xd7e37844, 0x22f49c35, 0x35016ffa, 0x11cd9c08, 0x53c99c04, 0x937231d8, 0xf98fc2de,  //
    0xeca6796f, 0x8242f123, 0x5f643f63, 0xc38c6b2d, 0x5a868f39, 0x2817781b, 0x9957b12b, 0x823911c5,  //
    0xd4572029, 0xee3c79c9, 0x8c9b4bae, 0xea2b4aff, 0xa21f900d, 0x21b28f3f, 0x6fb38d71, 0xb34163fa,  //
    0xd583ba99, 0xfa56f4d2, 0xf6c84890, 0xfaf041d2, 0xfed77bd5, 0x0091f266, 0xba51522f, 0xa06194c3,  //
    0xc18dea93, 0xc08ebf87, 0x86f94003, 0xa2b7dbe3, 0x4f5824eb, 0x05d16d31, 0x8bfd9a4e, 0x5713802e,  //
    0xaa2fa128, 0x5fdbaa3a, 0x9576ff0b, 0xd67314bc, 0xced4cc89, 0x3c102657, 0x82ae82eb, 0x4147a6cf,  //
    0x2872d754, 0x431a4ba3, 0x8ebb76ec, 0x41b110f2, 0xac7c2739, 0x1155dc19, 0x4dcf6c90, 0x11b5a957,  //
    0x4c21afba, 0x53510cc4, 0x7602a378, 0x91d6ae79, 0xb8de3f1b, 0xa51731b3, 0x1d430800, 0x2182fe42,  //
    0x1eac9f76, 0xc5981d8e, 0xea67720d, 0x01d71878, 0x8061b118, 0x42220506, 0x10733f24, 0x52f0ba44,  //
    0x859717ac, 0xcaa9e842, 0x23c2a0bb, 0x910953f3, 0xcc281d4a, 0x3fb1b6c2, 0x2260916e, 0xca356e92,  //
    0xd0a8cb2c, 0x5fbe08dd, 0x6ecf83da, 0x58612885, 0x6d24b014, 0x9679350a, 0xd5d5407b, 0x6364778e,  //
    0xd65b879e, 0xa3c562fb, 0x956e932f, 0x9b0e236d, 0x799b9447, 0x9173153e, 0x39aa9556, 0xd09754c7,  //
    0xc792546f, 0x4310d953, 0xde61638d, 0xe12c4c02, 0x18cd3bf0, 0x8dfcbc5a, 0x315fb781, 0xf67aadfd,  //
    0xec359d09, 0xf07ee9c7, 0xa387c332, 0x9fea64b2, 0xb9efa363, 0x46f00ff4, 0x75bc574e, 0x41d05fcb,  //
    0xac6d9b53, 0xadef0b9f, 0x282d02fc, 0x21ccaf5a, 0x0bf3ea13, 0x0d095678, 0x31b562ae, 0x4c536536,  //
    0x55285149, 0x856437c3, 0x3c706c9d, 0x7d97de29, 0xae626fd5, 0x4ac107b0, 0x3e35c520, 0xc6b61fdd,  //
    0x32ca6c3e, 0x7d1eaf6e, 0x6010ca3c, 0xb1b28f1c, 0x20530af4, 0x1d6c8b38, 0x176a85e8, 0xa1e9d548,  //
    0xc3808303, 0x7ae43e86, 0xd6cb2133, 0xed037923, 0x29c8946a, 0x4f0eb63b, 0xce88972e, 0x84be5e5c,  //
    0xbe45a401, 0x3723fbd1, 0x58082f51, 0xabaa854e, 0xeee793e1, 0xd76611b9, 0x11fb1efa, 0xd6ce23a4,  //
    0x959da13c, 0x3191229b, 0x59e78e72, 0xe6145924, 0xd94bd073, 0xa42d1f2d, 0xdfd03461, 0xd822afca,  //
    0xda33ac2b, 0xb77e95eb, 0xc49b85ba, 0x1dee0368, 0x5454567a, 0xfa4cf3c8, 0x95c26a91, 0x9c05d54f,  //
    0x24ec2661, 0xfbe506a2, 0x90096720, 0x129d5883, 0xfc1a405b, 0xbfd9309b, 0x32db629e, 0x4cd066e2,  //
    0xb6cd255b, 0x4f885377, 0x1cf93c3b, 0xf3ebf2af, 0x14be78ea, 0x772c091d, 0x9ff93da3, 0xdeac007b,  //
    0xfe49aa72, 0x324bd4a8, 0xd246c3c1, 0x1b59a5ca, 0x9a65e101, 0x7d2c8829, 0x3d20b650, 0x990d59cc,  //
    0x44db5a01, 0x210ec34c, 0xa1195164, 0x14eb0fd0, 0x7ecf599c, 0x493a6b52, 0x5c317ce9, 0x414b2853,  //
    0xa0d43984, 0x35633f53, 0xeede1882, 0xcc900c19, 0xafe5e2ca, 0x693a89f3, 0x71e2009d, 0xb4540545,  //
    0x2687a8c7, 0x37ec6aed, 0xc3b19955, 0xc1cf1745, 0x6ce9abdc, 0xbc929152, 0x1b440d2d, 0xa329f50f,  //
    0x17d02cab, 0xd61042c5, 0x5ed82699, 0xd33a02d3, 0xbf058c33, 0x38197332, 0xd22e17ab, 0x52cdaed8,  //
    0xc1002ea8, 0xa3708c99, 0x6ab67677, 0x47c89d64, 0x1796c0ea, 0xd007329b, 0x0241b432, 0x4f2f0be4,  //
    0x506f5155, 0x9b7fb3f1, 0xfe8adf2c, 0xcb594d19, 0x59e82962, 0xde045148, 0x419b15dd, 0xd5b4f36b,  //
    0x18f2aa18, 0xca3960fe, 0xe3aac567, 0xe1f25309, 0xc7542b4f, 0x368f586f, 0x21fc01aa, 0x1c81d4c2,  //
    0x59ff7d48, 0x31f61713, 0xd455a8b3, 0x33bda081, 0x2464e412, 0x1a0c7ad8, 0xb9511bfd, 0x8d005fcf,  //
    0x6ea08c9f, 0x591e96df, 0x7ef345c3, 0x21dbd533, 0xce3be279, 0xe061ec9c, 0x8b2d7454, 0xfb19cf1d,  //
    0xadd51e4e, 0xd2a73d69, 0xc8872f08, 0x41f6569a, 0xc4eed9ce, 0x2774da14, 0x6756121f, 0xaeacf748,  //
    0x1fb76f79, 0xde52d7b5, 0x49680f70, 0xacf4343b, 0x3cd12bfc, 0xfceee54e, 0x9c19d5b0, 0x8b351fda,  //
    0xbe0033c3, 0x3feb1c4e, 0x00599da3, 0xfd97db96, 0x5eafcf45, 0x96af2e20, 0x0ddf0f71, 0x247f13e5,  //
    0x2c419460, 0x12c20cfd, 0xe5667ce5, 0xff09f617, 0xb9b461e4, 0x10604f84, 0x94e73c54, 0x2fb5e88f,  //
    0xe8f35b6b, 0x70fe6e91, 0x5a521cc6, 0xf149f4ce, 0xf4290b22, 0x72ead464, 0x72af5466, 0x1222d01f,  //
    0x78b694a7, 0x22e33464, 0xc970a4c7, 0xcf2e50b2, 0x382b1b46, 0xfd729957, 0xefd4de1c, 0x630d5485,  //
    0xe4c2745a, 0x79e3a9c3, 0xf297c623, 0x17167e0c, 0xb0e843f6, 0x23a118aa, 0x09bc2bb3, 0x5eb0d32e   //
};

static uint32_t __attribute__((aligned(64), section(".l1"))) dump_u32[sizeof(data_u32) / 4];

int main() {
  unsigned long vl;

  // SEW 8
  {
    vuint8m1_t v_u8;
    vbool8_t   vm;

    vl   = __riscv_vsetvl_e8m1(sizeof(data_u32) / 4);
    v_u8 = __riscv_vle8_v_u8m1((uint8_t *)data_u32, vl);
    __riscv_vse8_v_u8m1((uint8_t *)dump_u32, v_u8, vl);
    v_u8 = __riscv_vlse8_v_u8m1((uint8_t *)data_u32, 2, vl);
    __riscv_vse8_v_u8m1((uint8_t *)dump_u32, v_u8, vl);
    v_u8 = __riscv_vlse8_v_u8m1((uint8_t *)data_u32, 3, vl);
    __riscv_vse8_v_u8m1((uint8_t *)dump_u32, v_u8, vl);
    v_u8 = __riscv_vlse8_v_u8m1((uint8_t *)data_u32, 4, vl);
    __riscv_vse8_v_u8m1((uint8_t *)dump_u32, v_u8, vl);

    vm   = __riscv_vlm_v_b8((uint8_t *)data_u32, vl);
    v_u8 = __riscv_vle8_v_u8m1_m(vm, (uint8_t *)data_u32, vl);
    __riscv_vse8_v_u8m1((uint8_t *)dump_u32, v_u8, vl);
    v_u8 = __riscv_vlse8_v_u8m1_m(vm, (uint8_t *)data_u32, 2, vl);
    __riscv_vse8_v_u8m1((uint8_t *)dump_u32, v_u8, vl);
    v_u8 = __riscv_vlse8_v_u8m1_m(vm, (uint8_t *)data_u32, 3, vl);
    __riscv_vse8_v_u8m1((uint8_t *)dump_u32, v_u8, vl);
    v_u8 = __riscv_vlse8_v_u8m1_m(vm, (uint8_t *)data_u32, 4, vl);
    __riscv_vse8_v_u8m1((uint8_t *)dump_u32, v_u8, vl);

    vl   = __riscv_vsetvl_e8m1(sizeof(data_u32) / 16);
    v_u8 = __riscv_vlse8_v_u8m1((uint8_t *)data_u32, 8, vl);
    __riscv_vse8_v_u8m1((uint8_t *)dump_u32, v_u8, vl);
    v_u8 = __riscv_vlse8_v_u8m1((uint8_t *)data_u32, 16, vl);
    __riscv_vse8_v_u8m1((uint8_t *)dump_u32, v_u8, vl);

    vm   = __riscv_vlm_v_b8((uint8_t *)data_u32, vl);
    v_u8 = __riscv_vlse8_v_u8m1_m(vm, (uint8_t *)data_u32, 8, vl);
    __riscv_vse8_v_u8m1((uint8_t *)dump_u32, v_u8, vl);
    v_u8 = __riscv_vlse8_v_u8m1_m(vm, (uint8_t *)data_u32, 16, vl);
    __riscv_vse8_v_u8m1((uint8_t *)dump_u32, v_u8, vl);

    vl   = __riscv_vsetvl_e8m1(sizeof(data_u32) / 4);
    v_u8 = __riscv_vle8_v_u8m1((uint8_t *)data_u32, vl);
    __riscv_vsse8_v_u8m1((uint8_t *)dump_u32, 2, v_u8, vl);
    __riscv_vsse8_v_u8m1((uint8_t *)dump_u32, 3, v_u8, vl);
    __riscv_vsse8_v_u8m1((uint8_t *)dump_u32, 4, v_u8, vl);

    vm = __riscv_vlm_v_b8((uint8_t *)data_u32, vl);
    __riscv_vsse8_v_u8m1_m(vm, (uint8_t *)dump_u32, 2, v_u8, vl);
    __riscv_vsse8_v_u8m1_m(vm, (uint8_t *)dump_u32, 3, v_u8, vl);
    __riscv_vsse8_v_u8m1_m(vm, (uint8_t *)dump_u32, 4, v_u8, vl);

    vl   = __riscv_vsetvl_e8m1(sizeof(data_u32) / 16);
    v_u8 = __riscv_vle8_v_u8m1((uint8_t *)data_u32, vl);
    __riscv_vsse8_v_u8m1((uint8_t *)dump_u32, 8, v_u8, vl);
    __riscv_vsse8_v_u8m1((uint8_t *)dump_u32, 16, v_u8, vl);

    vm = __riscv_vlm_v_b8((uint8_t *)data_u32, vl);
    __riscv_vsse8_v_u8m1_m(vm, (uint8_t *)dump_u32, 8, v_u8, vl);
    __riscv_vsse8_v_u8m1_m(vm, (uint8_t *)dump_u32, 16, v_u8, vl);

    // segment loads and stores
    vuint8m1x3_t v_u8x3;
    vuint8m1x4_t v_u8x4;

    vl     = __riscv_vsetvl_e8m1(sizeof(data_u32) / 4);
    v_u8x4 = __riscv_vlseg4e8_v_u8m1x4((uint8_t *)data_u32, vl);
    __riscv_vse8_v_u8m1((uint8_t *)dump_u32, __riscv_vget_v_u8m1x4_u8m1(v_u8x4, 0), vl);
    __riscv_vse8_v_u8m1((uint8_t *)dump_u32, __riscv_vget_v_u8m1x4_u8m1(v_u8x4, 1), vl);
    __riscv_vse8_v_u8m1((uint8_t *)dump_u32, __riscv_vget_v_u8m1x4_u8m1(v_u8x4, 2), vl);
    __riscv_vse8_v_u8m1((uint8_t *)dump_u32, __riscv_vget_v_u8m1x4_u8m1(v_u8x4, 3), vl);

    vm     = __riscv_vlm_v_b8((uint8_t *)data_u32, vl);
    v_u8x4 = __riscv_vlseg4e8_v_u8m1x4_m(vm, (uint8_t *)data_u32, vl);
    __riscv_vse8_v_u8m1((uint8_t *)dump_u32, __riscv_vget_v_u8m1x4_u8m1(v_u8x4, 0), vl);
    __riscv_vse8_v_u8m1((uint8_t *)dump_u32, __riscv_vget_v_u8m1x4_u8m1(v_u8x4, 1), vl);
    __riscv_vse8_v_u8m1((uint8_t *)dump_u32, __riscv_vget_v_u8m1x4_u8m1(v_u8x4, 2), vl);
    __riscv_vse8_v_u8m1((uint8_t *)dump_u32, __riscv_vget_v_u8m1x4_u8m1(v_u8x4, 3), vl);

    vl     = __riscv_vsetvl_e8m1(sizeof(data_u32) / 16);
    v_u8x4 = __riscv_vlsseg4e8_v_u8m1x4((uint8_t *)data_u32, 8, vl);
    __riscv_vse8_v_u8m1((uint8_t *)dump_u32, __riscv_vget_v_u8m1x4_u8m1(v_u8x4, 0), vl);
    __riscv_vse8_v_u8m1((uint8_t *)dump_u32, __riscv_vget_v_u8m1x4_u8m1(v_u8x4, 1), vl);
    __riscv_vse8_v_u8m1((uint8_t *)dump_u32, __riscv_vget_v_u8m1x4_u8m1(v_u8x4, 2), vl);
    __riscv_vse8_v_u8m1((uint8_t *)dump_u32, __riscv_vget_v_u8m1x4_u8m1(v_u8x4, 3), vl);

    vm     = __riscv_vlm_v_b8((uint8_t *)data_u32, vl);
    v_u8x4 = __riscv_vlsseg4e8_v_u8m1x4_m(vm, (uint8_t *)data_u32, 8, vl);
    __riscv_vse8_v_u8m1((uint8_t *)dump_u32, __riscv_vget_v_u8m1x4_u8m1(v_u8x4, 0), vl);
    __riscv_vse8_v_u8m1((uint8_t *)dump_u32, __riscv_vget_v_u8m1x4_u8m1(v_u8x4, 1), vl);
    __riscv_vse8_v_u8m1((uint8_t *)dump_u32, __riscv_vget_v_u8m1x4_u8m1(v_u8x4, 2), vl);
    __riscv_vse8_v_u8m1((uint8_t *)dump_u32, __riscv_vget_v_u8m1x4_u8m1(v_u8x4, 3), vl);

    v_u8x4 = __riscv_vlsseg4e8_v_u8m1x4((uint8_t *)data_u32, 16, vl);
    __riscv_vse8_v_u8m1((uint8_t *)dump_u32, __riscv_vget_v_u8m1x4_u8m1(v_u8x4, 0), vl);
    __riscv_vse8_v_u8m1((uint8_t *)dump_u32, __riscv_vget_v_u8m1x4_u8m1(v_u8x4, 1), vl);
    __riscv_vse8_v_u8m1((uint8_t *)dump_u32, __riscv_vget_v_u8m1x4_u8m1(v_u8x4, 2), vl);
    __riscv_vse8_v_u8m1((uint8_t *)dump_u32, __riscv_vget_v_u8m1x4_u8m1(v_u8x4, 3), vl);

    v_u8x4 = __riscv_vlsseg4e8_v_u8m1x4_m(vm, (uint8_t *)data_u32, 16, vl);
    __riscv_vse8_v_u8m1((uint8_t *)dump_u32, __riscv_vget_v_u8m1x4_u8m1(v_u8x4, 0), vl);
    __riscv_vse8_v_u8m1((uint8_t *)dump_u32, __riscv_vget_v_u8m1x4_u8m1(v_u8x4, 1), vl);
    __riscv_vse8_v_u8m1((uint8_t *)dump_u32, __riscv_vget_v_u8m1x4_u8m1(v_u8x4, 2), vl);
    __riscv_vse8_v_u8m1((uint8_t *)dump_u32, __riscv_vget_v_u8m1x4_u8m1(v_u8x4, 3), vl);

    vl     = __riscv_vsetvl_e8m1(sizeof(data_u32) / 4);
    v_u8x4 = __riscv_vset_v_u8m1_u8m1x4(v_u8x4, 0, __riscv_vle8_v_u8m1((uint8_t *)data_u32, vl));
    v_u8x4 = __riscv_vset_v_u8m1_u8m1x4(v_u8x4, 1, __riscv_vle8_v_u8m1((uint8_t *)data_u32, vl));
    v_u8x4 = __riscv_vset_v_u8m1_u8m1x4(v_u8x4, 2, __riscv_vle8_v_u8m1((uint8_t *)data_u32, vl));
    v_u8x4 = __riscv_vset_v_u8m1_u8m1x4(v_u8x4, 3, __riscv_vle8_v_u8m1((uint8_t *)data_u32, vl));
    __riscv_vsseg4e8_v_u8m1x4((uint8_t *)dump_u32, v_u8x4, vl);

    vm = __riscv_vlm_v_b8((uint8_t *)data_u32, vl);
    __riscv_vsseg4e8_v_u8m1x4_m(vm, (uint8_t *)dump_u32, v_u8x4, vl);

    vl     = __riscv_vsetvl_e8m1(sizeof(data_u32) / 16);
    v_u8x4 = __riscv_vset_v_u8m1_u8m1x4(v_u8x4, 0, __riscv_vle8_v_u8m1((uint8_t *)data_u32, vl));
    v_u8x4 = __riscv_vset_v_u8m1_u8m1x4(v_u8x4, 1, __riscv_vle8_v_u8m1((uint8_t *)data_u32, vl));
    v_u8x4 = __riscv_vset_v_u8m1_u8m1x4(v_u8x4, 2, __riscv_vle8_v_u8m1((uint8_t *)data_u32, vl));
    v_u8x4 = __riscv_vset_v_u8m1_u8m1x4(v_u8x4, 3, __riscv_vle8_v_u8m1((uint8_t *)data_u32, vl));
    __riscv_vssseg4e8_v_u8m1x4((uint8_t *)dump_u32, 8, v_u8x4, vl);
    __riscv_vssseg4e8_v_u8m1x4((uint8_t *)dump_u32, 16, v_u8x4, vl);

    vm = __riscv_vlm_v_b8((uint8_t *)data_u32, vl);
    __riscv_vssseg4e8_v_u8m1x4_m(vm, (uint8_t *)dump_u32, 8, v_u8x4, vl);
    __riscv_vssseg4e8_v_u8m1x4_m(vm, (uint8_t *)dump_u32, 16, v_u8x4, vl);

    // vector loads and stores that are not aligned to the width of the memory ports
    vl     = __riscv_vsetvl_e8m1(sizeof(data_u32) / 4);
    v_u8x3 = __riscv_vlseg3e8_v_u8m1x3((uint8_t *)data_u32, vl);
    v_u8x3 = __riscv_vset_v_u8m1_u8m1x3(v_u8x3, 0, __riscv_vle8_v_u8m1(((uint8_t *)data_u32) + 1, vl));
    v_u8x3 = __riscv_vset_v_u8m1_u8m1x3(v_u8x3, 1, __riscv_vle8_v_u8m1((uint8_t *)data_u32, vl));
    v_u8x3 = __riscv_vset_v_u8m1_u8m1x3(v_u8x3, 2, __riscv_vle8_v_u8m1((uint8_t *)data_u32, vl));
    __riscv_vsseg3e8_v_u8m1x3(((uint8_t *)dump_u32) + 1, v_u8x3, vl);

    vm = __riscv_vlm_v_b8((uint8_t *)data_u32, vl);
    __riscv_vsseg3e8_v_u8m1x3_m(vm, ((uint8_t *)dump_u32) + 1, v_u8x3, vl);

    v_u8x3 = __riscv_vlseg3e8_v_u8m1x3(((uint8_t *)data_u32) + 1, vl);
    __riscv_vse8_v_u8m1(((uint8_t *)dump_u32) + 1, __riscv_vget_v_u8m1x3_u8m1(v_u8x3, 0), vl);
    __riscv_vse8_v_u8m1((uint8_t *)dump_u32, __riscv_vget_v_u8m1x3_u8m1(v_u8x3, 1), vl);
    __riscv_vse8_v_u8m1((uint8_t *)dump_u32, __riscv_vget_v_u8m1x3_u8m1(v_u8x3, 2), vl);

    v_u8x3 = __riscv_vlseg3e8_v_u8m1x3_m(vm, ((uint8_t *)data_u32) + 1, vl);
    __riscv_vse8_v_u8m1(((uint8_t *)dump_u32) + 1, __riscv_vget_v_u8m1x3_u8m1(v_u8x3, 0), vl);
    __riscv_vse8_v_u8m1((uint8_t *)dump_u32, __riscv_vget_v_u8m1x3_u8m1(v_u8x3, 1), vl);
    __riscv_vse8_v_u8m1((uint8_t *)dump_u32, __riscv_vget_v_u8m1x3_u8m1(v_u8x3, 2), vl);
  }

  // SEW 16
  {
    vuint16m1_t v_u16;
    vbool16_t   vm;

    vl    = __riscv_vsetvl_e16m1(sizeof(data_u32) / 8);
    v_u16 = __riscv_vle16_v_u16m1((uint16_t *)data_u32, vl);
    __riscv_vse16_v_u16m1((uint16_t *)dump_u32, v_u16, vl);
    v_u16 = __riscv_vlse16_v_u16m1((uint16_t *)data_u32, 4, vl);
    __riscv_vse16_v_u16m1((uint16_t *)dump_u32, v_u16, vl);
    v_u16 = __riscv_vlse16_v_u16m1((uint16_t *)data_u32, 6, vl);
    __riscv_vse16_v_u16m1((uint16_t *)dump_u32, v_u16, vl);
    v_u16 = __riscv_vlse16_v_u16m1((uint16_t *)data_u32, 8, vl);
    __riscv_vse16_v_u16m1((uint16_t *)dump_u32, v_u16, vl);

    vm    = __riscv_vlm_v_b16((uint8_t *)data_u32, vl);
    v_u16 = __riscv_vle16_v_u16m1_m(vm, (uint16_t *)data_u32, vl);
    __riscv_vse16_v_u16m1((uint16_t *)dump_u32, v_u16, vl);
    v_u16 = __riscv_vlse16_v_u16m1_m(vm, (uint16_t *)data_u32, 4, vl);
    __riscv_vse16_v_u16m1((uint16_t *)dump_u32, v_u16, vl);
    v_u16 = __riscv_vlse16_v_u16m1_m(vm, (uint16_t *)data_u32, 6, vl);
    __riscv_vse16_v_u16m1((uint16_t *)dump_u32, v_u16, vl);
    v_u16 = __riscv_vlse16_v_u16m1_m(vm, (uint16_t *)data_u32, 8, vl);
    __riscv_vse16_v_u16m1((uint16_t *)dump_u32, v_u16, vl);

    vl    = __riscv_vsetvl_e16m1(sizeof(data_u32) / 32);
    v_u16 = __riscv_vlse16_v_u16m1((uint16_t *)data_u32, 16, vl);
    __riscv_vse16_v_u16m1((uint16_t *)dump_u32, v_u16, vl);
    v_u16 = __riscv_vlse16_v_u16m1((uint16_t *)data_u32, 32, vl);
    __riscv_vse16_v_u16m1((uint16_t *)dump_u32, v_u16, vl);

    vm    = __riscv_vlm_v_b16((uint8_t *)data_u32, vl);
    v_u16 = __riscv_vlse16_v_u16m1_m(vm, (uint16_t *)data_u32, 16, vl);
    __riscv_vse16_v_u16m1((uint16_t *)dump_u32, v_u16, vl);
    v_u16 = __riscv_vlse16_v_u16m1_m(vm, (uint16_t *)data_u32, 32, vl);
    __riscv_vse16_v_u16m1((uint16_t *)dump_u32, v_u16, vl);

    vl    = __riscv_vsetvl_e16m1(sizeof(data_u32) / 8);
    v_u16 = __riscv_vle16_v_u16m1((uint16_t *)data_u32, vl);
    __riscv_vsse16_v_u16m1((uint16_t *)dump_u32, 4, v_u16, vl);
    __riscv_vsse16_v_u16m1((uint16_t *)dump_u32, 6, v_u16, vl);
    __riscv_vsse16_v_u16m1((uint16_t *)dump_u32, 8, v_u16, vl);

    vm = __riscv_vlm_v_b16((uint8_t *)data_u32, vl);
    __riscv_vsse16_v_u16m1_m(vm, (uint16_t *)dump_u32, 4, v_u16, vl);
    __riscv_vsse16_v_u16m1_m(vm, (uint16_t *)dump_u32, 6, v_u16, vl);
    __riscv_vsse16_v_u16m1_m(vm, (uint16_t *)dump_u32, 8, v_u16, vl);

    vl    = __riscv_vsetvl_e16m1(sizeof(data_u32) / 32);
    v_u16 = __riscv_vle16_v_u16m1((uint16_t *)data_u32, vl);
    __riscv_vsse16_v_u16m1((uint16_t *)dump_u32, 16, v_u16, vl);
    __riscv_vsse16_v_u16m1((uint16_t *)dump_u32, 32, v_u16, vl);

    vm = __riscv_vlm_v_b16((uint8_t *)data_u32, vl);
    __riscv_vsse16_v_u16m1_m(vm, (uint16_t *)dump_u32, 16, v_u16, vl);
    __riscv_vsse16_v_u16m1_m(vm, (uint16_t *)dump_u32, 32, v_u16, vl);

    // segment loads and stores
    vuint16m1x3_t v_u16x3;
    vuint16m1x4_t v_u16x4;

    vl      = __riscv_vsetvl_e16m1(sizeof(data_u32) / 8);
    v_u16x4 = __riscv_vlseg4e16_v_u16m1x4((uint16_t *)data_u32, vl);
    __riscv_vse16_v_u16m1((uint16_t *)dump_u32, __riscv_vget_v_u16m1x4_u16m1(v_u16x4, 0), vl);
    __riscv_vse16_v_u16m1((uint16_t *)dump_u32, __riscv_vget_v_u16m1x4_u16m1(v_u16x4, 1), vl);
    __riscv_vse16_v_u16m1((uint16_t *)dump_u32, __riscv_vget_v_u16m1x4_u16m1(v_u16x4, 2), vl);
    __riscv_vse16_v_u16m1((uint16_t *)dump_u32, __riscv_vget_v_u16m1x4_u16m1(v_u16x4, 3), vl);

    vm      = __riscv_vlm_v_b16((uint8_t *)data_u32, vl);
    v_u16x4 = __riscv_vlseg4e16_v_u16m1x4_m(vm, (uint16_t *)data_u32, vl);
    __riscv_vse16_v_u16m1((uint16_t *)dump_u32, __riscv_vget_v_u16m1x4_u16m1(v_u16x4, 0), vl);
    __riscv_vse16_v_u16m1((uint16_t *)dump_u32, __riscv_vget_v_u16m1x4_u16m1(v_u16x4, 1), vl);
    __riscv_vse16_v_u16m1((uint16_t *)dump_u32, __riscv_vget_v_u16m1x4_u16m1(v_u16x4, 2), vl);
    __riscv_vse16_v_u16m1((uint16_t *)dump_u32, __riscv_vget_v_u16m1x4_u16m1(v_u16x4, 3), vl);

    vl      = __riscv_vsetvl_e16m1(sizeof(data_u32) / 32);
    v_u16x4 = __riscv_vlsseg4e16_v_u16m1x4((uint16_t *)data_u32, 16, vl);
    __riscv_vse16_v_u16m1((uint16_t *)dump_u32, __riscv_vget_v_u16m1x4_u16m1(v_u16x4, 0), vl);
    __riscv_vse16_v_u16m1((uint16_t *)dump_u32, __riscv_vget_v_u16m1x4_u16m1(v_u16x4, 1), vl);
    __riscv_vse16_v_u16m1((uint16_t *)dump_u32, __riscv_vget_v_u16m1x4_u16m1(v_u16x4, 2), vl);
    __riscv_vse16_v_u16m1((uint16_t *)dump_u32, __riscv_vget_v_u16m1x4_u16m1(v_u16x4, 3), vl);

    vm      = __riscv_vlm_v_b16((uint8_t *)data_u32, vl);
    v_u16x4 = __riscv_vlsseg4e16_v_u16m1x4_m(vm, (uint16_t *)data_u32, 16, vl);
    __riscv_vse16_v_u16m1((uint16_t *)dump_u32, __riscv_vget_v_u16m1x4_u16m1(v_u16x4, 0), vl);
    __riscv_vse16_v_u16m1((uint16_t *)dump_u32, __riscv_vget_v_u16m1x4_u16m1(v_u16x4, 1), vl);
    __riscv_vse16_v_u16m1((uint16_t *)dump_u32, __riscv_vget_v_u16m1x4_u16m1(v_u16x4, 2), vl);
    __riscv_vse16_v_u16m1((uint16_t *)dump_u32, __riscv_vget_v_u16m1x4_u16m1(v_u16x4, 3), vl);

    vl      = __riscv_vsetvl_e16m1(sizeof(data_u32) / 8);
    v_u16x4 = __riscv_vset_v_u16m1_u16m1x4(v_u16x4, 0, __riscv_vle16_v_u16m1((uint16_t *)data_u32, vl));
    v_u16x4 = __riscv_vset_v_u16m1_u16m1x4(v_u16x4, 1, __riscv_vle16_v_u16m1((uint16_t *)data_u32, vl));
    v_u16x4 = __riscv_vset_v_u16m1_u16m1x4(v_u16x4, 2, __riscv_vle16_v_u16m1((uint16_t *)data_u32, vl));
    v_u16x4 = __riscv_vset_v_u16m1_u16m1x4(v_u16x4, 3, __riscv_vle16_v_u16m1((uint16_t *)data_u32, vl));
    __riscv_vsseg4e16_v_u16m1x4((uint16_t *)dump_u32, v_u16x4, vl);

    vm = __riscv_vlm_v_b16((uint8_t *)data_u32, vl);
    __riscv_vsseg4e16_v_u16m1x4_m(vm, (uint16_t *)dump_u32, v_u16x4, vl);

    vl      = __riscv_vsetvl_e16m1(sizeof(data_u32) / 32);
    v_u16x4 = __riscv_vset_v_u16m1_u16m1x4(v_u16x4, 0, __riscv_vle16_v_u16m1((uint16_t *)data_u32, vl));
    v_u16x4 = __riscv_vset_v_u16m1_u16m1x4(v_u16x4, 1, __riscv_vle16_v_u16m1((uint16_t *)data_u32, vl));
    v_u16x4 = __riscv_vset_v_u16m1_u16m1x4(v_u16x4, 2, __riscv_vle16_v_u16m1((uint16_t *)data_u32, vl));
    v_u16x4 = __riscv_vset_v_u16m1_u16m1x4(v_u16x4, 3, __riscv_vle16_v_u16m1((uint16_t *)data_u32, vl));
    __riscv_vssseg4e16_v_u16m1x4((uint16_t *)dump_u32, 16, v_u16x4, vl);
    __riscv_vssseg4e16_v_u16m1x4((uint16_t *)dump_u32, 32, v_u16x4, vl);

    vm = __riscv_vlm_v_b16((uint8_t *)data_u32, vl);
    __riscv_vssseg4e16_v_u16m1x4_m(vm, (uint16_t *)dump_u32, 16, v_u16x4, vl);
    __riscv_vssseg4e16_v_u16m1x4_m(vm, (uint16_t *)dump_u32, 32, v_u16x4, vl);

    // vector loads and stores that are not aligned to the width of the memory ports
    vl      = __riscv_vsetvl_e16m1(sizeof(data_u32) / 8);
    v_u16x3 = __riscv_vlseg3e16_v_u16m1x3((uint16_t *)data_u32, vl);
    v_u16x3 = __riscv_vset_v_u16m1_u16m1x3(v_u16x3, 0, __riscv_vle16_v_u16m1(((uint16_t *)data_u32) + 1, vl));
    v_u16x3 = __riscv_vset_v_u16m1_u16m1x3(v_u16x3, 1, __riscv_vle16_v_u16m1((uint16_t *)data_u32, vl));
    v_u16x3 = __riscv_vset_v_u16m1_u16m1x3(v_u16x3, 2, __riscv_vle16_v_u16m1((uint16_t *)data_u32, vl));
    __riscv_vsseg3e16_v_u16m1x3(((uint16_t *)dump_u32) + 1, v_u16x3, vl);

    vm = __riscv_vlm_v_b16((uint8_t *)data_u32, vl);
    __riscv_vsseg3e16_v_u16m1x3_m(vm, ((uint16_t *)dump_u32) + 1, v_u16x3, vl);

    v_u16x3 = __riscv_vlseg3e16_v_u16m1x3(((uint16_t *)data_u32) + 1, vl);
    __riscv_vse16_v_u16m1(((uint16_t *)dump_u32) + 1, __riscv_vget_v_u16m1x3_u16m1(v_u16x3, 0), vl);
    __riscv_vse16_v_u16m1((uint16_t *)dump_u32, __riscv_vget_v_u16m1x3_u16m1(v_u16x3, 1), vl);
    __riscv_vse16_v_u16m1((uint16_t *)dump_u32, __riscv_vget_v_u16m1x3_u16m1(v_u16x3, 2), vl);

    v_u16x3 = __riscv_vlseg3e16_v_u16m1x3_m(vm, ((uint16_t *)data_u32) + 1, vl);
    __riscv_vse16_v_u16m1(((uint16_t *)dump_u32) + 1, __riscv_vget_v_u16m1x3_u16m1(v_u16x3, 0), vl);
    __riscv_vse16_v_u16m1((uint16_t *)dump_u32, __riscv_vget_v_u16m1x3_u16m1(v_u16x3, 1), vl);
    __riscv_vse16_v_u16m1((uint16_t *)dump_u32, __riscv_vget_v_u16m1x3_u16m1(v_u16x3, 2), vl);
  }

  // SEW 32
  {
    vuint32m1_t v_u32;
    vbool32_t   vm;

    vl    = __riscv_vsetvl_e32m1(sizeof(data_u32) / 16);
    v_u32 = __riscv_vle32_v_u32m1(data_u32, vl);
    __riscv_vse32_v_u32m1(dump_u32, v_u32, vl);
    v_u32 = __riscv_vlse32_v_u32m1(data_u32, 8, vl);
    __riscv_vse32_v_u32m1(dump_u32, v_u32, vl);
    v_u32 = __riscv_vlse32_v_u32m1(data_u32, 12, vl);
    __riscv_vse32_v_u32m1(dump_u32, v_u32, vl);
    v_u32 = __riscv_vlse32_v_u32m1(data_u32, 16, vl);
    __riscv_vse32_v_u32m1(dump_u32, v_u32, vl);

    vm    = __riscv_vlm_v_b32((uint8_t *)data_u32, vl);
    v_u32 = __riscv_vle32_v_u32m1_m(vm, data_u32, vl);
    __riscv_vse32_v_u32m1(dump_u32, v_u32, vl);
    v_u32 = __riscv_vlse32_v_u32m1_m(vm, data_u32, 8, vl);
    __riscv_vse32_v_u32m1(dump_u32, v_u32, vl);
    v_u32 = __riscv_vlse32_v_u32m1_m(vm, data_u32, 12, vl);
    __riscv_vse32_v_u32m1(dump_u32, v_u32, vl);
    v_u32 = __riscv_vlse32_v_u32m1_m(vm, data_u32, 16, vl);
    __riscv_vse32_v_u32m1(dump_u32, v_u32, vl);

    vl    = __riscv_vsetvl_e32m1(sizeof(data_u32) / 64);
    v_u32 = __riscv_vlse32_v_u32m1(data_u32, 32, vl);
    __riscv_vse32_v_u32m1(dump_u32, v_u32, vl);
    v_u32 = __riscv_vlse32_v_u32m1(data_u32, 64, vl);
    __riscv_vse32_v_u32m1(dump_u32, v_u32, vl);

    vm    = __riscv_vlm_v_b32((uint8_t *)data_u32, vl);
    v_u32 = __riscv_vlse32_v_u32m1_m(vm, data_u32, 32, vl);
    __riscv_vse32_v_u32m1(dump_u32, v_u32, vl);
    v_u32 = __riscv_vlse32_v_u32m1_m(vm, data_u32, 64, vl);
    __riscv_vse32_v_u32m1(dump_u32, v_u32, vl);

    vl    = __riscv_vsetvl_e32m1(sizeof(data_u32) / 16);
    v_u32 = __riscv_vle32_v_u32m1(data_u32, vl);
    __riscv_vsse32_v_u32m1(dump_u32, 8, v_u32, vl);
    __riscv_vsse32_v_u32m1(dump_u32, 12, v_u32, vl);
    __riscv_vsse32_v_u32m1(dump_u32, 16, v_u32, vl);

    vm = __riscv_vlm_v_b32((uint8_t *)data_u32, vl);
    __riscv_vsse32_v_u32m1_m(vm, dump_u32, 8, v_u32, vl);
    __riscv_vsse32_v_u32m1_m(vm, dump_u32, 12, v_u32, vl);
    __riscv_vsse32_v_u32m1_m(vm, dump_u32, 16, v_u32, vl);

    vl    = __riscv_vsetvl_e32m1(sizeof(data_u32) / 64);
    v_u32 = __riscv_vle32_v_u32m1(data_u32, vl);
    __riscv_vsse32_v_u32m1(dump_u32, 32, v_u32, vl);
    __riscv_vsse32_v_u32m1(dump_u32, 64, v_u32, vl);

    vm = __riscv_vlm_v_b32((uint8_t *)data_u32, vl);
    __riscv_vsse32_v_u32m1_m(vm, dump_u32, 32, v_u32, vl);
    __riscv_vsse32_v_u32m1_m(vm, dump_u32, 64, v_u32, vl);

    // segment loads and stores
    vuint32m1x2_t v_u32x2;

    vl      = __riscv_vsetvl_e32m1(sizeof(data_u32) / 16);
    v_u32x2 = __riscv_vlseg2e32_v_u32m1x2(data_u32, vl);
    __riscv_vse32_v_u32m1(dump_u32, __riscv_vget_v_u32m1x2_u32m1(v_u32x2, 0), vl);
    __riscv_vse32_v_u32m1(dump_u32, __riscv_vget_v_u32m1x2_u32m1(v_u32x2, 1), vl);

    vm      = __riscv_vlm_v_b32((uint8_t *)data_u32, vl);
    v_u32x2 = __riscv_vlseg2e32_v_u32m1x2_m(vm, data_u32, vl);
    __riscv_vse32_v_u32m1(dump_u32, __riscv_vget_v_u32m1x2_u32m1(v_u32x2, 0), vl);
    __riscv_vse32_v_u32m1(dump_u32, __riscv_vget_v_u32m1x2_u32m1(v_u32x2, 1), vl);

    vl      = __riscv_vsetvl_e32m1(sizeof(data_u32) / 8);
    v_u32x2 = __riscv_vset_v_u32m1_u32m1x2(v_u32x2, 0, __riscv_vle32_v_u32m1(data_u32, vl));
    v_u32x2 = __riscv_vset_v_u32m1_u32m1x2(v_u32x2, 1, __riscv_vle32_v_u32m1(data_u32, vl));
    __riscv_vsseg2e32_v_u32m1x2(dump_u32, v_u32x2, vl);

    vm = __riscv_vlm_v_b32((uint8_t *)data_u32, vl);
    __riscv_vsseg2e32_v_u32m1x2_m(vm, dump_u32, v_u32x2, vl);

    // vector loads and stores that are not aligned to the width of the memory ports
    vl      = __riscv_vsetvl_e32m1(sizeof(data_u32) / 16);
    v_u32x2 = __riscv_vset_v_u32m1_u32m1x2(v_u32x2, 0, __riscv_vle32_v_u32m1(data_u32 + 1, vl));
    v_u32x2 = __riscv_vset_v_u32m1_u32m1x2(v_u32x2, 1, __riscv_vle32_v_u32m1(data_u32, vl));
    __riscv_vsseg2e32_v_u32m1x2(dump_u32 + 1, v_u32x2, vl);

    vm = __riscv_vlm_v_b32((uint8_t *)data_u32, vl);
    __riscv_vsseg2e32_v_u32m1x2_m(vm, dump_u32 + 1, v_u32x2, vl);

    v_u32x2 = __riscv_vlseg2e32_v_u32m1x2(data_u32 + 1, vl);
    __riscv_vse32_v_u32m1(dump_u32 + 1, __riscv_vget_v_u32m1x2_u32m1(v_u32x2, 0), vl);
    __riscv_vse32_v_u32m1(dump_u32, __riscv_vget_v_u32m1x2_u32m1(v_u32x2, 1), vl);

    v_u32x2 = __riscv_vlseg2e32_v_u32m1x2_m(vm, data_u32 + 1, vl);
    __riscv_vse32_v_u32m1(dump_u32 + 1, __riscv_vget_v_u32m1x2_u32m1(v_u32x2, 0), vl);
    __riscv_vse32_v_u32m1(dump_u32, __riscv_vget_v_u32m1x2_u32m1(v_u32x2, 1), vl);
  }

  return 0;
}
