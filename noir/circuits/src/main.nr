use dep::std;
// use std::str;
//use std::collections::HashMap;


fn crop(o_step : Field, t_step : Field, w_start : Field, h_start: Field, original: [Field; 12], transformed: [Field; 4]) {
    let t_array_size = transformed.len()
    let t_array_height = t_array_size / t_step; 

    for i in 0..t_array_height {
        for j in 0..t_step
        original[(h_start+i)*step + w_start]
    };
    //     for &col_idx in &columns_to_compare {
    //         // Check if the indices are within the bounds of the respective matrices
    //         if row_idx < matrix1.len() && col_idx < matrix1[row_idx].len() &&
    //            row_idx < matrix2.len() && col_idx < matrix2[row_idx].len() {
    //             // Compare the elements at the specified indices
    //             if matrix1[row_idx][col_idx] != matrix2[row_idx][col_idx] {
    //                 return false; // Elements at the specified indices are not equal
    //             }
    //         } else {
    //             return false; // Indices are out of bounds for one or both matrices
    //         }
    //     }
    // }
    
    // vec![0; length]
//     for height in transformed {
// 		for &num in height { {
// 			for (var k = 0; k < 3; k++) {
// 				transformed[i][j][k] === original[hStartNew + i][wStartNew + j][k];	
// 			}		
// 		}		
// 	}
// }

// component main {public[hash]}= Crop(720, 1280, 480, 640, 100, 100);


// #[test]
// fn test_main() {
//     main(1, 2);

    // Uncomment to make test fail
    // main(1, 1);
}

fn main(orig: pub [Field; 12], tran: pub [Field; 4]) {
    let step: Field = 3;
    let start: Field = 4;
    crop(step, start, orig, tran);
    std::println("done");
}