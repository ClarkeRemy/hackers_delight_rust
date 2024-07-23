#![no_implicit_prelude]
#![no_std]



// tasks
//
// 32 bit (whole book)
// use traits to make generic
// see if it will extend to simd
//
// extra tasks, get used to binary/hex representation


extern crate core;

pub use chapter_2::*;
pub mod chapter_2{
 /// 2-1
  pub mod Manipulationg_Rightmost_Bits {
    extern crate core;
    use core::num::Wrapping as W;
    #[allow(non_camel_case_types)]
    pub type wu32 = W<u32>;

    #[cfg(test)]use core::{assert_eq, assert_ne};
    #[cfg(test)]#[test]fn _1(){
      let x = W(0b_0101_1000);                 assert_eq!(x, W(0x58));
      let y = clear_lowest_one(x);
      assert_eq!(y, W(0b_0101_0000));          assert_eq!(y, W(0x50));
      assert_ne!(y, W(0)) // x is not a power of two or 0
    }



    pub fn clear_lowest_one(x:wu32)->wu32{ x & x-W(1) }

    #[cfg(test)]#[test]fn _2(){
      let x = W(0b_1010_0111);                assert_eq!(x, W(0xA7));
      let y = set_lowest_zero(x);
      assert_eq!(y, W(0b_1010_1111));         assert_eq!(y, W(0xAF));
    }
    pub fn set_lowest_zero(x:W<u32>)->W<u32> {x | x+W(1)}
    

    #[cfg(test)]#[test]fn _3(){
      let x = W(0b_1010_0111);                 assert_eq!(x, W(0xA7));
      let y = clear_trailing_ones(x);
      assert_eq!(y, W(0b_1010_0000));          assert_eq!(y, W(0xA0));
      assert_ne!(y, W(0)); // x is not 2n-1
    }
    pub fn clear_trailing_ones(x:wu32)->wu32 {x & x+W(1)}

    
    #[cfg(test)]#[test]fn _4(){
      let x = W(0b_1010_1000);                 assert_eq!(x, W(0xA8));
      let y = set_trailing_zeros(x);        
      assert_eq!(y, W(0b_1010_1111));          assert_eq!(y, W(0xAF));
    }
    pub fn set_trailing_zeros(x:wu32)->wu32 {x | x-W(1)}
  

    #[cfg(test)]#[test]fn _5(){
      let x = W(0b_1010_0111);                 assert_eq!(x, W(0xA7));
      let y = mask_last_zero(x);
      assert_eq!(y, W(0b_0000_1000));          assert_eq!(y, W(0x08));
    }
    pub fn mask_last_zero(x:wu32)->wu32 {!x & x+W(1)}

    
    #[cfg(test)]#[test]fn _6(){
      let x = W(0b_1010_1000);                 assert_eq!(x, W(0xA8));
      let y = mask_but_last_one(x);
      assert_eq!(y, !W(0b_0000_1000_u32));
      assert_eq!(y, W(0xFF_FF_FF_F7));
    }
    pub fn mask_but_last_one(x:wu32)->wu32 {!x | x-W(1)}


    #[cfg(test)]#[test]fn _7(){
      let x = W(0b_0101_1000);                 assert_eq!(x, W(0x58));
      let funs = [
        mask_trailing_zeros_1,
        mask_trailing_zeros_2, 
        mask_trailing_zeros_3
      ];
      for f in funs {
        let y = f(x);
        assert_eq!(y, W(0b_0000_0111));        assert_eq!(y, W(0x07));
      }
    }
    pub fn mask_trailing_zeros_1(x:wu32)->wu32{!x  & x-W(1)}
    pub fn mask_trailing_zeros_2(x:wu32)->wu32{!(x | -x)}
    pub fn mask_trailing_zeros_3(x:wu32)->wu32{ (x & -x)-W(1)}


    #[cfg(test)]#[test]fn _8(){
      let x = W(0b_1010_0111);                 assert_eq!(x, W(0xA7));
      let y = mask_but_trailing_ones(x);
      assert_eq!(y, !W(0b_0000_0111_u32));
      assert_eq!(y, W(0xFF_FF_FF_F8));
    }
    pub fn mask_but_trailing_ones(x:wu32)->wu32 {!x | x+W(1)}

    #[cfg(test)]#[test]fn _9(){
      let x = W(0b_0101_1000);                 assert_eq!(x, W(0x58));
      let y = mask_last_one(x);
      assert_eq!(y, W(0b_0000_1000));          assert_eq!(y, W(0x08));
    }
    pub fn mask_last_one(x:wu32)->wu32 {x & -x}

 
    #[cfg(test)]#[test]fn _10(){
      let x = W(0b_0101_1000);                 assert_eq!(x, W(0x58));
      let y = mask_from_last_one(x);
      assert_eq!(y, W(0b_0000_1111));          assert_eq!(y, W(0x0F));

      let x = W(0);
      let y = mask_from_last_one(x);
      assert_eq!(y, !W(0_u32));

      let x = !W(0_u32);
      let y = mask_from_last_one(x);
      assert_eq!(y, W(1));
    }
    pub fn mask_from_last_one(x:wu32)->wu32 {x ^ x-W(1)}

    
    #[cfg(test)]#[test]fn _11(){
      let x = W(0b_0101_0111);                 assert_eq!(x, W(0x57));
      let y = mask_from_last_zero(x);
      assert_eq!(y, W(0b_0000_1111));          assert_eq!(y, W(0x0F));

      let x = !W(0_u32);
      let y = mask_from_last_zero(x);
      assert_eq!(y, x);

      let x = W(0);
      let y = mask_from_last_zero(x);
      assert_eq!(y, W(1));
    }
    pub fn mask_from_last_zero(x:wu32)->wu32 {x ^ x+W(1)}


    #[cfg(test)]#[test]fn _12(){
      let x = W(0b_0101_1100);                 assert_eq!(x, W(0x5C));
      let funs = [
        clear_lowest_string_ones_1,
        clear_lowest_string_ones_2,
      ];
      for f in funs {
        let y = f(x);
        assert_eq!(y, W(0b_0100_0000));        assert_eq!(y, W(0x40));
      }
    }
    pub fn clear_lowest_string_ones_1(x:wu32)->wu32 {(x | x-W(1))+W(1) & x}
    pub fn clear_lowest_string_ones_2(x:wu32)->wu32 {(x & -x)+x & x}

    // De Morgan's Laws extended
    #[cfg(test)]#[test]fn _13(){
      use assert_eq as eq;
      for _x in 0_u8..u8::MAX{ let x = W(_x);
        for _y in 0_u8..u8::MAX{ let y = W(_y);

          eq!( !(x & y) , !x | !y ); // De Morgan 1
          eq!( !(x | y) , !x & !y ); // De Morgan 2

          eq!( !(x+W(1)), !x-W(1) ); 
          eq!( !(x-W(1)), !x+W(1) );
          eq!( !-x      , x-W(1)  );
          eq!( !(x ^ y) , !x ^ y  ); // no builtin bit-eq

          eq!( !(x+y)   , !x-y    );
          eq!( !(x-y)   , !x+y    );
        }
      }
    }

    // A Novel Application
    #[cfg(test)]#[test]fn _14(){
      let x = [
        W(0b_011_0_1111_0000_u32), // note the top 3 bits add up to 2
        W(0b_101_0_1111_0000),
        W(0b_110_0_1111_0000),
      ];
      let y = x.map(bit_set_next);
      
      assert_eq!( y[0], W(0b_011_1_0000_0111) );
      assert_eq!( y[1], W(0b_101_1_0000_0111) );
      assert_eq!( y[2], W(0b_110_1_0000_0111) );
    }
    pub fn bit_set_next(x:wu32)->wu32{
      if x == W(0){return x;} // avoid division by zero

      let s = x&-x;           // smallest bit
      let r = s+x;            // ripple carry lowest string of ones
      
      r | ((x ^ r) >> 2)/s    // in one line, (top bits | bottom bits)
    }
  }
  /// 2-2
  pub mod Addition_Combined_with_Logical_Operators {
    extern crate core;
    use core::num::Wrapping as W;
    #[allow(non_camel_case_types)]
    pub type wu32 = W<u32>;
    
    #[cfg(test)]use core::{assert_eq};
    #[cfg(test)]#[test]fn _1(){
    use assert_eq as eq;
      for _x in 0_u8..u8::MAX{ let x = W(_x);
        for _y in 0_u8..u8::MAX{ let y = W(_y);

          eq!( -x     , !x+W(1)      ); 
          // note te following is the inverse operations
          eq!( -x     , !(x-W(1))    );
          // because negation is it's own inverse the undoing is equivalent to doing so...
          eq!( !x+W(1), !(x-W(1))    );

          eq!( !x     , -x-W(1)      );
          eq!( !x     , !x+W(1)-W(1) ); // understood as

          eq!( -!x    , x+W(1)       );
          eq!( -!x    , !!x+W(1)     ); //understood as

          eq!( !-x    , x-W(1)        );
          eq!( !-x    , !(!x+W(1))    ); // breaking it down
          eq!( !-x    , !!(x-W(1))    );

          eq!( x+y    , x-!y-W(1)            );
          eq!( x+y    , (x ^ y)+W(2)*(x & y) ); // non-carries + carries
          eq!( x+y    , (x | y)+(x & y)      ); // no_carry_add then induce carries
          eq!( x+y    , W(2)*(x | y)-(x ^ y) ); // carry_all - non_carries
        
          eq!( x-y    , x+!y+W(1)            );
          eq!( x-y    , (  x   ^   y  )-W(2)*(!x & y)); // start with this identity : (x+y)-2*y
          eq!( x-y    , ((x&!y)|(!x&y))-W(2)*(!x & y));

          eq!( x-y    , (x & !y)-(!x & y)    ); // bits_unique_to_x - bits_unique_to_y
          eq!( x-y    , W(2)*(x & !y)-(  x   ^   y  )); 
          eq!( x-y    , W(2)*(x & !y)-((x&!y)|(!x&y))); 

          eq!( x ^ y  , (x | y)-(x & y)      );
          eq!( x & !y , (x | y)-y            );
          eq!( x & !y , x-(x & y)            );
          
          eq!( !(x-y), y-x-W(1)         );
          eq!( !(x-y), !x+y             );
        
          eq!( !(x ^ y), (x & y)-(x | y)-W(1));
          eq!( !(x ^ y), !((x | y)-(x & y))); // !(x&y) & (x|y)
          eq!( !(x ^ y), (x & y)+!(x | y));

          eq!( x | y   , (x & !y) + y      );
          eq!( x & y   , (!x | y) -!x      );
        }
      }
    }


  }
  /// 2-3
  pub mod Inequalities_among_Logical_Arithmetic_Expressions {
    extern crate core;
    use core::num::Wrapping as W;
    #[allow(non_camel_case_types)]
    pub type wu32 = W<u32>;
    
    #[cfg(test)]#[test]fn _1(){
    }
   // wild wizard binary op table function
   //  https://gist.github.com/m1el/4cbf714815c5efefa6353d3d95275778
  }
  /// 2-4
  pub mod Absolute_Value_Function {
    extern crate core;
    use core::num::Wrapping as W;
    #[allow(non_camel_case_types)]
    pub type wi32 = W<i32>;
    
    #[cfg(test)]use core::assert_eq;
    #[cfg(test)]#[test]fn _1(){
      // let x = W(i32::MIN);
      // assert_ne!(abs(x),W(i32::MIN)); fail case

      let x = W(-10_i32);
      assert_eq!(W(10), ((x>>((x.0^x.0).count_zeros()-2)as usize)|W(1))*x);
      
    }
    fn abs(x:wi32)->wi32 {
      let l = ((x^x).0.count_zeros() -1) as usize;
      let y = x >> l ; // the compiler knows  if x >= 0 { 0 } else { -1 }
      (x ^ y)-y 
      // x+y ^ y      // when y=-1 =>  !(x-1) = -x
      // x-(W(2)*x & y)  // when y=-1 => x-2x
    }
    fn nabs(x:wi32)->wi32 {
      let l = ((x^x).0.count_zeros() -1) as usize;
      let y = x >> l ; // the compiler knows  if x >= 0 { 0 } else { -1 }
      y-(x ^ y) 
      // y-x ^ y     // ^-1  ==> !
      // (W(2)*x & y)-x
    }
  }
  /// 2-5
  pub mod Average_of_Two_Integers {
    extern crate core;
    use core::num::Wrapping as W;
    #[allow(non_camel_case_types)]
    pub type wu8 = W<u8>; // using bytes instead for testing purposes
    pub type wi8 = W<i8>;
    
    #[cfg(test)]use core::assert_eq;
    #[cfg(test)]#[test]fn _1(){
      for _x in 0_u8..u8::MAX{ let x = W(_x);
        for _y in 0_u8..u8::MAX{ let y = W(_y);
          let r = [floor_average_u_1, average_u_2].map(|f|f(x,y));
          assert!(x<=r[0]&& y>=r[0] || x>=r[0]&& y<=r[0] );
        }
      }
      for _x in 0_i8..i8::MAX{ let x = W(_x);
        for _y in 0_i8..i8::MAX{ let y = W(_y);
          let r = [average_s_1, average_s_2].map(|f|f(x,y));
          assert!(x<=r[0]&& y>=r[0] || x>=r[0]&& y<=r[0] );
        }
      }

      assert_eq!(average_s_to_zero(W(0), W(-1)),W(0))
    }
    pub fn floor_average_u_1(x: wu8, y: wu8)->wu8{
      (x & y)+((x ^ y)>>1)} // carries/2 + non_carries/2
    pub fn average_u_2(x: wu8, y: wu8)->wu8{
      (x | y)-((x ^ y)>>1)} // all_adds_carry/2 -carries/2
    pub fn average_s_1(x: wi8, y: wi8)->wi8{
      (x & y)+((x ^ y)>>1)} // carries/2 + non_carries/2
    pub fn average_s_2(x: wi8, y: wi8)->wi8{
      (x | y)-((x ^ y)>>1)} // all_adds_carry/2 -carries/2

    pub fn average_s_to_zero(x: wi8, y: wi8)->wi8{
     let t = average_s_1(x, y);
     t+(W((t.0 as u8 >> (i8::BITS-1)as usize) as i8) & (x ^ y))
    }
  }

  /// 2-6
  pub mod Sign_Extension {
    extern crate core;
    use core::num::Wrapping as W;
    #[cfg(test)]use core::{assert_eq, assert_ne};
    #[cfg(test)]#[test]fn _1(){
      #![allow(overflowing_literals)]
      assert_eq!(0x_ff_i8 as u8 as u32, 0x_ff_u32); // ensure that sign extention does not happen

      for _x in 0..i8::MAX {
        let x = [sign_extend_1, sign_extend_2, sign_extend_3].map(|f|f(W(_x)));
        let t = W(_x as u8 as i32);
        for i in 0..x.len() {assert_eq!(x[i],t);}
      }
    }
    // this sign extends 8 bits to 32 bits
    pub fn sign_extend_1(x:W<i8>)->W<i32>{
      W((((x.0 as u8) as u32 +0x_80 & 0x_FF) - 0x_80) as i32)
    }
    pub fn sign_extend_2(x:W<i8>)->W<i32>{
      W((((x.0 as u8 as u32 & 0x_FF) ^ 0x_80) - 0x_80) as i32)
    }
    pub fn sign_extend_3(x:W<i8>)->W<i32>{
      let _x = x.0 as u8 as u32;
      W((_x & 0x_7F) as i32) - W((_x & 0x_80) as i32)
    }
  }
  /// 2-7
  pub mod Shift_Right_Signed_from_Unsigned {
    extern crate core;
    use core::num::Wrapping as W;
    #[cfg(test)]use core::assert_eq;
    #[cfg(test)]#[test]fn _1(){
      for _x in i8::MIN..i8::MAX{
        let x = W(_x);
        for n in 0..=i8::BITS as usize {
          [
           shift_right_signed_1,
           shift_right_signed_2,
           shift_right_signed_3,
           shift_right_signed_4,
           shift_right_signed_5,
          ].map(|f| f(x,n)).map(|r|{
            let neg = r.0.is_negative();
            assert!(!neg && r<=x || neg && x<=r, 
              "\nx : {x:?}\nr : {r:?}\npos : {neg}\nn : {n}\nSIGN : {SIGN}"
            );
          });
          assert_eq!( 
            W((W(SIGN as u8) >> n).0 as i8), 
            W(1_i8) << (W(31_usize)-W(n)).0 
          );
        }
      }
    }

    const SIGN : i8 = i8::MIN;
    pub fn shift_right_signed_1(x:W<i8>, n:usize)->W<i8>{
      if n >=i8::BITS as usize { return if x.0&SIGN == SIGN{ W(-1) } else { W(0) }};

      W((((W(x.0 as u8)+W(SIGN as u8)) >> n) - (W(SIGN as u8)>>n)).0 as i8)
    }
    pub fn shift_right_signed_2(x:W<i8>, n:usize)->W<i8>{
      if n >=i8::BITS as usize { return if x.0&SIGN == SIGN{ W(-1) } else { W(0) }};

      let t = W(SIGN as u8) >>n;
      W( (( (W(x.0 as u8) >> n) ^ t)-t).0 as i8 )
    }
    pub fn shift_right_signed_3(x:W<i8>, n:usize)->W<i8>{
      if n >=i8::BITS as usize { return if x.0&SIGN == SIGN{ W(-1) } else { W(0) }};

      let t = (x.0 & SIGN) as u8 >>n;
      W( ( (W(x.0 as u8) >> n) - (W(t)+W(t))).0 as i8 )
    }
    
    pub fn shift_right_signed_4(x:W<i8>, n:usize)->W<i8>{
      if n >=i8::BITS as usize { return if x.0&SIGN == SIGN{ W(-1) } else { W(0) }};
      let shift :usize = (i8::BITS-1) as usize;
      W((
        (W(x.0 as u8) >> n) 
        | 
        (-(W(x.0 as u8) >> shift) << shift-n)
      ).0 as i8 )
    }
    pub fn shift_right_signed_5(x:W<i8>, n:usize)->W<i8>{
      if n >=i8::BITS as usize { return if x.0&SIGN == SIGN{ W(-1) } else { W(0) }};

      let t = -(W(x.0 as u8 >> (u8::BITS -1)as usize));
      W((((W(x.0 as u8)^t)>>n)^t).0 as i8)
    }
  }

  /// 2-8
  pub mod Sign_Function {
    extern crate core;
    use core::num::Wrapping as W;
    #[cfg(test)]use core::assert_eq;
    #[cfg(test)]#[test]fn _1(){
      for _x in i8::MIN..i8::MAX {
      let x = W(_x);
      [
        signum_1,
        signum_2,
        signum_3,
        signum_4,
        signum_5,
      ].map(|f|f(x)).map(|v|
        assert_eq!(W(_x.signum()), v));
    }  
    }
    const SHIFT : usize =(i8::BITS-1)as usize;
    pub fn signum_1(x:W<i8>)->W<i8>{
      (x>>SHIFT) | W((-W(x.0 as u8)>>SHIFT).0 as i8)
    }
    pub fn signum_2(x:W<i8>)->W<i8>{
      -W((W(x.0 as u8)>>SHIFT).0 as i8) // makes the sign extension
      |
      W((-W(x.0 as u8)>>SHIFT).0 as i8) // last bit
    }
    pub fn signum_3(x:W<i8>)->W<i8>{
      W((x>W(0)) as i8) - W((x<W(0)) as i8)
    }
    pub fn signum_4(x:W<i8>)->W<i8>{
      W((x>=W(0)) as i8) - W((x<=W(0)) as i8)
    }
    pub fn signum_5(x:W<i8>)->W<i8>{
      if x.0==i8::MIN {return W(-1);}
      W((-W(x.0 as u8)>>SHIFT).0 as i8)
      -
      W((W(x.0 as u8)>>SHIFT).0 as i8) // last bit
    }
  }
  /// 2-8
  pub mod Three_Value {
    extern crate core;
    use core::num::Wrapping as W;
    #[cfg(test)]use core::assert_eq;
    #[cfg(test)]#[test]fn _1(){
      for _x in i8::MIN..i8::MAX { let x = W(_x);
        for _y in i8::MIN..i8::MAX { let y = W(_y);
          use core::cmp::{Ordering::*, Ord};
          [cmp_1,cmp_2].map(|f|f(x,y)).map(|v|
            assert_eq!(
              match Ord::cmp(&_x, &_y) {
                Greater=>W(1),
                Equal  =>W(0),
                Less   =>W(-1),
              },
              v
          ));
        }
      }    
    }
    pub fn cmp_1(x:W<i8>,y:W<i8>)->W<i8>{
      W((x>y) as i8) - W((x<y) as i8)
    }
    pub fn cmp_2(x:W<i8>,y:W<i8>)->W<i8>{
      W((x>=y) as i8) - W((x<=y) as i8)
    }
    /*
      000 y
      001 x 

      y - x
      000 + 111 + 001     

      r5= 001 + 111 + 001 = 001
      r6= 000 + 110 + 001 = 111 carry=0
      r7= 001 + 111 + 000 = 000 carry=1
      r8= 001 + 111 + 001 = 001           carry=1


      000 y
      000 x 

      r5= 000 + 111 + 001 = 000
      r6= 000 + 111 + 001 = 000 carry=1
      r7= 000 + 111 + 001 = 000 carry=1
      r8= 000 + 111 + 001 = 000            carry=1


      001 y
      000 x 

      r5= 000 + 110 + 001 = 111
      r6= 001 + 111 + 001 = 001 carry=1
      r7= 000 + 110 + 001 = 111 carry=0
      r8= 111 + 000 + 000 = 111            carry=0

    */
  }

  /// 2-10
  pub mod Transfer_of_Sign_Functon {
    extern crate core;
    use core::num::Wrapping as W;
    #[cfg(test)]use core::assert_eq;
    #[cfg(test)]#[test]fn _1(){
      for _x in i8::MIN+1..i8::MAX { let x = W(_x);
        for _y in i8::MIN+1..i8::MAX { let y = W(_y);
          [
            isign_1a,
            isign_1b,
            isign_2a,
            // isign_2b,
          ].map(|f|f(x,y)).map(|v|{assert_eq!(v,
              if y.0.signum()==0 {W(x.0.abs())}
              else               {W(x.0.abs()) * W(y.0.signum())},
              "\nx: {_x}\ny: {_y}"
          )});
        }
      }
    }
    const SHIFT : usize = i8::BITS as usize -1;
    pub fn isign_1a(x:W<i8>,y:W<i8>)->W<i8>{
      let t = y >> SHIFT;
      (W(x.0.abs()) ^ t)-t   // (^) (-1) = !
                             // (-) (-1) = + 1
                             // !x + 1  if t = -1 
                             // !(x - 1) = !x+1
    }
    pub fn isign_1b(x:W<i8>,y:W<i8>)->W<i8>{
      let t = y >> SHIFT;
      (W(x.0.abs()) + t)^t
    }
    pub fn isign_2a(x:W<i8>,y:W<i8>)->W<i8>{
      let t = (x ^ y) >> SHIFT; // diff=>-1 , same=>0
      (x ^ t)-t
    }
    pub fn isign_2b(x:W<i8>,y:W<i8>)->W<i8>{
      let t = (x ^ y) >> SHIFT;
      (x + t) ^ t
    }
  }
  /// 2-11
  pub mod Decoding_a_Zero_Means_2_pow_n_Field {
    extern crate core;
    use core::num::Wrapping as W;
    #[cfg(test)]use core::assert_eq;
    #[cfg(test)]#[test]fn _1(){
      for _x in u8::MIN..u8::MAX { let x = W(_x);
        [
          decode_zero_means_0x40_v1,
          decode_zero_means_0x40_v2,
          decode_zero_means_0x40_v3,
          decode_zero_means_0x40_v4,
          // decode_zero_means_0x40_v5,
          decode_zero_means_0x40_v6,
          decode_zero_means_0x40_v7,
          // decode_zero_means_0x40_v8,
        ].map(|f|f(x)).map(|v|assert_eq!(
          v, if x&MASK==W(0){CARRY_BIT} else { x&MASK}, "\nx: {_x:08b} :: {_x}"
        ));
      }
    }
    // if one byte, 0x_00_u8 means 0x100
    // the following is for decoding (because encoding is just a mask)
    const CARRY_BIT : W<u8> = W(1_u8<<u8::BITS-2);
    const MASK : W<u8> = W(CARRY_BIT.0-1);
    pub fn decode_zero_means_0x40_v1(x:W<u8>)->W<u8>{
      (x-W(1)& MASK)+W(1)
    }
    pub fn decode_zero_means_0x40_v2(x:W<u8>)->W<u8>{
      ((x+MASK)| -CARRY_BIT)+CARRY_BIT+W(1)
    }
    pub fn decode_zero_means_0x40_v3(x:W<u8>)->W<u8>{
      CARRY_BIT-(-x & MASK)
    }
    pub fn decode_zero_means_0x40_v4(x:W<u8>)->W<u8>{
      ((x+MASK)&MASK)+W(1)
    }
    pub fn decode_zero_means_0x40_v5(x:W<u8>)->W<u8>{
      ((x+MASK)|CARRY_BIT)-MASK // does not clear junk!
    }
    pub fn decode_zero_means_0x40_v6(x:W<u8>)->W<u8>{
      -(-x|-CARRY_BIT) // -CARRY_BIT = !MASK
    } 
    pub fn decode_zero_means_0x40_v7(x:W<u8>)->W<u8>{
      ((x-W(1))| -CARRY_BIT)+CARRY_BIT+W(1)
    } 
    pub fn decode_zero_means_0x40_v8(x:W<u8>)->W<u8>{
      ((x-W(1)) & CARRY_BIT)+x  // does not clear junk!
    } 
   
   
  }


  /// 2-12
  pub mod Comparison_Predicates {
    extern crate core;
    use core::{num::Wrapping as W};
    #[cfg(test)]use core::assert_eq;
    #[cfg(test)]#[test]fn _1(){
      for _x in i8::MIN..i8::MAX { let x = W(_x);
        for _y in i8::MIN..i8::MAX { let y = W(_y);
          [
            equal_1,
            equal_2,
            equal_3,
            equal_4,
            equal_5,
          ].map(|f|f(x,y)).map(|v|assert_eq!(
            W((v.0 as u8 >> (u8::BITS-1) as usize) as i8),
            W((x==y) as i8) 
          ));
        }
      }
    }
    // the following will require shifting to inspect sign bit
    pub fn equal_1(x:W<i8>, y:W<i8>)->W<i8>{ abs(x-y)-W(1) }
    pub fn equal_2(x:W<i8>, y:W<i8>)->W<i8>{ abs(x-y+W(i8::MIN)) }
    pub fn equal_3(x:W<i8>, y:W<i8>)->W<i8>{ 
      W(((x-y).0.leading_zeros()
         << 
        i8::BITS - i8::BITS.trailing_zeros() -1
      ) as i8 )
    }
    pub fn equal_4(x:W<i8>, y:W<i8>)->W<i8>{ 
      -W(((x-y).0.leading_zeros() 
         >> 
         i8::BITS.trailing_zeros()) as i8
       )
    }
    pub fn equal_5(x:W<i8>, y:W<i8>)->W<i8>{ !(x-y | y-x)}

    // helper functions

    fn abs(x:W<i8>)->W<i8> {
      let shift = (i8::BITS -1) as usize;
      let y = x >> shift ; 
      (x ^ y)-y 
      // x+y ^ y 
      // x-(W(2)*x & y)
    }
    fn nabs(x:W<i8>)->W<i8> {
      let shift = (i8::BITS -1) as usize;
      let y = x >> shift ;
      y-(x ^ y) 
      // y-x ^ y
      // (W(2)*x & y)-x
    }
  }
}





#[cfg(test)]
mod tests {
    use super::*;
    use core::assert_eq;

    #[test]
    fn it_works() {
    }
}

