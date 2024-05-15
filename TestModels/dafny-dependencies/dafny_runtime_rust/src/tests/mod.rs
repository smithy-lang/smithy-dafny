pub mod experimental;
// Test module
#[cfg(test)]
mod tests {
    use crate::rcmut::RcMut;

    use crate::*;

    #[test]
    fn test_int() {
        let x = int!(37);
        assert_eq!(x.to_u8().unwrap(), truncate!(x.clone(), u8));
        assert_eq!(x.to_u16().unwrap(), truncate!(x.clone(), u16));
        assert_eq!(x.to_u32().unwrap(), truncate!(x.clone(), u32));
        assert_eq!(x.to_u64().unwrap(), truncate!(x.clone(), u64));
        assert_eq!(x.to_u128().unwrap(), truncate!(x.clone(), u128));
        assert_eq!(x.to_i8().unwrap(), truncate!(x.clone(), i8));
        assert_eq!(x.to_i16().unwrap(), truncate!(x.clone(), i16));
        assert_eq!(x.to_i32().unwrap(), truncate!(x.clone(), i32));
        assert_eq!(x.to_i64().unwrap(), truncate!(x.clone(), i64));
        assert_eq!(x.to_i128().unwrap(), truncate!(x.clone(), i128));
    }

    #[test]
    fn test_sequence() {
        let values = vec![1, 2, 3];
        let seq = Sequence::<i32>::from_array_owned(values.clone());
        assert_eq!(seq.cardinality_usize(), 3);
        assert_eq!(seq.to_array(), values.into());

        // Create a concat array, wrap it into a lazy one, get the i-th element,
        // and verify that this operation flattened the array
        let left = Sequence::<i32>::from_array_owned(vec![1, 2, 3]);
        let right = Sequence::<i32>::from_array_owned(vec![4, 5, 6]);
        let concat = Sequence::<i32>::new_concat_sequence(&left, &right);

        assert_eq!(concat.cardinality_usize(), 6);
        match &concat {
            Sequence::ConcatSequence {
                boxed,
                length,
                left,
                ..
            } => {
                assert_eq!(*length, 6);
                assert_eq!(unsafe { &*left.get() }.cardinality_usize(), 3);
                // Test that boxed is None
                assert!(boxed.as_ref().clone().borrow().as_ref().is_none());
            }
            _ => panic!("This should never happen"),
        }
        let value = concat.get_usize(0);
        assert_eq!(value, 1);
        match &concat {
            crate::Sequence::ConcatSequence { boxed, .. } => {
                assert_eq!(
                    *boxed.as_ref().clone().borrow().as_ref().unwrap().as_ref(),
                    vec![1, 2, 3, 4, 5, 6]
                );
            }
            _ => panic!("This should never happen"),
        }
    }

    #[test]
    fn test_dafny_int() {
        assert_eq!(int!(0).to_usize(), Some(0));
        assert_eq!(int!(42).to_usize(), Some(42));
    }

    #[test]
    fn test_dafny_sequence_print() {
        let hello: DafnyString = seq![
            DafnyChar('H'),
            DafnyChar('e'),
            DafnyChar('l'),
            DafnyChar('l'),
            DafnyChar('o')
        ];
        assert_eq!(DafnyPrintWrapper(&hello).to_string(), "Hello");
        let hello: DafnyStringUTF16 = seq![
            DafnyCharUTF16(0x0048),
            DafnyCharUTF16(0x0065),
            DafnyCharUTF16(0x006c),
            DafnyCharUTF16(0x006c),
            DafnyCharUTF16(0x006f)
        ];
        assert_eq!(DafnyPrintWrapper(&hello).to_string(), "Hello");
        assert_eq!(DafnyPrintWrapper(&string_of("Hello")).to_string(), "Hello");
        let hello = seq![1, 2, 3];
        assert_eq!(DafnyPrintWrapper(&hello).to_string(), "[1, 2, 3]");
    }
    #[test]
    fn test_dafny_sequence() {
        let s = seq![55, 56, 57];
        assert_eq!(seq![55, 56] != s, true);
        assert_eq!(s.cardinality_usize(), 3);
        assert_eq!(s.cardinality(), int!(3));
        assert_eq!(s.get(&int!(1)), 56);
        assert_eq!(s.slice(&int!(1), &int!(2)), seq![56]);
        assert_eq!(s.take(&int!(2)), seq![55, 56]);
        assert_eq!(s.drop(&int!(1)), seq![56, 57]);
        assert_eq!(s.update_index(&int!(1), &8), seq![55, 8, 57]);
        assert_eq!(s.concat(&seq![58, 59]), seq!(55, 56, 57, 58, 59));
    }

    #[test]
    fn test_dafny_set() {
        let s = set! {55, 56, 57, 56, 58};
        let t = set! {59, 58, 57};
        assert_eq!(s.cardinality_usize(), 4);
        assert_eq!(s.cardinality(), int!(4));
        assert_eq!(s.contains(&55), true);
        assert_eq!(s.contains(&54), false);
        assert_eq!(s.merge(&set! {}), s);
        assert_eq!(set! {}.merge(&s), s);
        assert_eq!(s.merge(&t), set! {59, 58, 57, 56, 55});
        assert_eq!(s.intersect(&t), set! {57, 58});
        assert_eq!(s.subtract(&set! {}), s);
        assert_eq!(set! {}.subtract(&s), set! {});
        let smt = s.subtract(&t);
        assert_eq!(smt, set! {55, 56});
        assert_eq!(t.subtract(&s), set! {59});
        assert_eq!(s.disjoint(&set! {}), true);
        assert_eq!(set! {}.disjoint(&s), true);
        assert_eq!(s.disjoint(&t), false);
        assert_eq!(t.disjoint(&s), false);
        assert_eq!(smt.disjoint(&t), true);
        assert_eq!(t.disjoint(&smt), true);
        assert_eq!(s.elements(), s);
        assert_eq!(
            s.as_dafny_multiset(),
            Multiset::from_array(&vec!(55, 56, 57, 58))
        );
    }

    #[test]
    fn test_dafny_multiset() {
        let s = multiset! {55, 56, 57, 56, 58};
        let t = multiset! {59, 58, 57, 56};
        assert_eq!(s.cardinality_usize(), 5);
        assert_eq!(s.cardinality(), int!(5));
        assert_eq!(s.contains(&55), true);
        assert_eq!(s.contains(&54), false);
        assert_eq!(s.get(&54), int!(0));
        assert_eq!(s.get(&55), int!(1));
        assert_eq!(s.get(&56), int!(2));
        assert_eq!(s.get(&57), int!(1));
        assert_eq!(s.merge(&multiset! {}), s);
        assert_eq!(multiset! {}.merge(&s), s);
        let merged = multiset! {59, 58, 58, 57, 57, 56, 56, 56, 55};
        assert_eq!(s.merge(&t), merged);
        assert_eq!(merged.cardinality_usize(), 9);
        assert_eq!(s.intersect(&t), multiset! {57, 58, 56});
        assert_eq!(s.subtract(&multiset! {}), s);
        assert_eq!(multiset! {}.subtract(&s), multiset! {});
        let smt = s.subtract(&t);
        assert_eq!(smt, multiset! {55, 56});
        let tms = t.subtract(&s);
        assert_eq!(tms, multiset! {59});
        assert_eq!(s.disjoint(&multiset! {}), true);
        assert_eq!(multiset! {}.disjoint(&s), true);
        assert_eq!(s.disjoint(&t), false);
        assert_eq!(t.disjoint(&s), false);
        assert_eq!(smt.disjoint(&t), false);
        assert_eq!(t.disjoint(&smt), false);
        assert_eq!(tms.disjoint(&s), true);
        assert_eq!(s.disjoint(&tms), true);
        assert_eq!(s.as_dafny_multiset(), s);
    }

    #[test]
    fn test_dafny_map() {
        let m_empty: Map<i32, i32> = map![];
        let m_3 = map![1 => 2, 3 => 6, 5 => 10];
        let k_3 = set! {1, 3, 5};
        let v_3 = set! {2, 6, 10};
        assert_eq!(m_empty.cardinality_usize(), 0);
        assert_eq!(m_empty.cardinality(), int!(0));
        assert_eq!(m_3.cardinality_usize(), 3);
        assert_eq!(m_3.cardinality(), int!(3));
        assert_eq!(m_3.contains(&1), true);
        assert_eq!(m_3.contains(&0), false);
        assert_eq!(m_3.keys(), k_3);
        assert_eq!(m_3.values(), v_3);
        assert_eq!(m_3.get(&1), 2);
        assert_eq!(m_3.get_or_none(&1), Some(2));
        assert_eq!(m_3.get_or_none(&0), None);
        let mut m_4 = m_3.update_index(&0, &2);
        assert_eq!(m_3.contains(&0), false);
        assert_eq!(m_4.contains(&0), true);
        m_4 = m_4.update_index_owned(0, 7);
        assert_eq!(m_4.contains(&0), true);

        assert_eq!(m_4.get(&0), 7);
        assert_eq!(m_4.cardinality_usize(), 4);
        assert_eq!(m_4.merge(&map![]), m_4);
        assert_eq!(map![].merge(&m_4), m_4);
        let m_5 = m_4.merge(&map![3 => 9, 6 => 12]);
        assert_eq!(m_5.cardinality_usize(), 5);
        println!("m_4 is {:?}", m_4);
        assert_eq!(m_4.get(&3), 6);
        assert_eq!(m_5.get(&3), 9);
        assert_eq!(m_5.subtract(&set! {}), m_5);
        let m_4b = m_5.subtract(&set! {3});
        assert_eq!(m_4b.cardinality_usize(), 4);
        assert_eq!(m_4b.contains(&3), false)
    }

    #[test]
    fn test_dafny_array() {
        let a = array![1, 2, 3];
        assert_eq!(crate::array::length_usize(a), 3);
        assert_eq!(crate::array::length(a), int!(3));
        assert_eq!(array::get_usize(a, 0), 1);
        assert_eq!(array::get_usize(a, 1), 2);
        assert_eq!(array::get_usize(a, 2), 3);
        array::update_usize(a, 0, 4);
        array::update_usize(a, 1, 5);
        array::update_usize(a, 2, 6);
        assert_eq!(array::get_usize(a, 0), 4);
        assert_eq!(array::get_usize(a, 1), 5);
        assert_eq!(array::get_usize(a, 2), 6);
        deallocate(a);
    }

    #[test]
    fn test_dafny_array_init() {
        // test from_vec, and initialize
        let mut v = Vec::new();
        v.push(1);
        v.push(2);
        v.push(3);
        let a = array::from_vec(v);
        assert_eq!(array::length_usize(a), 3);
        assert_eq!(array::get_usize(a, 0), 1);
        let v2 = array::initialize_usize(3, Rc::new(|i| i + 1));
        assert_eq!(array::length_usize(v2), 3);
        assert_eq!(array::get_usize(v2, 0), 1);
        assert_eq!(array::get_usize(v2, 1), 2);
        assert_eq!(array::get_usize(v2, 2), 3);
        array::update_usize(v2, 1, 10);
        assert_eq!(array::get_usize(v2, 1), 10);

        let v3 = array::initialize(&int!(3), Rc::new(|i| i.clone() + int!(1)));
        assert_eq!(array::length_usize(v3), 3);
        assert_eq!(array::get_usize(v3, 0), int!(1));
        assert_eq!(array::get_usize(v3, 1), int!(2));
        assert_eq!(array::get_usize(v3, 2), int!(3));
        array::update(v3, &int!(1), int!(10));
        assert_eq!(array::get_usize(v3, 1), int!(10));
    }

    #[test]
    fn test_array2() {
        let p = Array2::<DafnyInt>::placebos(&int!(3), &int!(4));
        for i in 0..3 {
            for j in 0..4 {
                modify!(p).data[i][j] = MaybeUninit::new(int!(i + j));
            }
        }
        let p = Array2::construct(p);
        assert_eq!(read!(p).length0_usize(), 3);
        assert_eq!(read!(p).length1_usize(), 4);
        let v = read!(p).to_vec();
        assert_eq!(v.len(), 3);
        assert_eq!(v, vec![
            vec![int!(0), int!(1), int!(2), int!(3)],
              vec![int!(1), int!(2), int!(3), int!(4)],
              vec![int!(2), int!(3), int!(4), int!(5)]]);

        deallocate(p);
        // Allocate an array whose first dimension is zero
        let p = Array2::<DafnyInt>::placebos(&int!(0), &int!(4));
        let p = Array2::construct(p);
        assert_eq!(read!(p).length0_usize(), 0);
        assert_eq!(read!(p).length1_usize(), 4);
        deallocate(p);
    }

    #[test]
    fn test_array3() {
        let a = Array3::<DafnyInt>::placebos(&int!(3), &int!(2), &int!(4));
        for i in 0..3 {
            for j in 0..2 {
                for k in 0..4 {
                    modify!(a).data[i][j][k] = MaybeUninit::new(DafnyInt::from(i * j + k));
                }
            }
        }
        let a = Array3::construct(a);
        assert_eq!(read!(a).length0(), int!(3));
        assert_eq!(read!(a).length1(), int!(2));
        assert_eq!(read!(a).length2(), int!(4));
        let v = read!(a).to_vec();
        assert_eq!(v.len(), 3);
        for i in 0..3 {
            for j in 0..2 {
                for k in 0..4 {
                    assert_eq!(read!(a).data[i][j][k], DafnyInt::from(i * j + k));
                    assert_eq!(v[i][j][k], DafnyInt::from(i * j + k));
                }
            }
        }
        deallocate(a);
        // Even if the first two dimensions are zero, the third dimension should not be zero
        let a = Array3::<DafnyInt>::placebos(&int!(0), &int!(0), &int!(4));
        let a = Array3::construct(a);
        assert_eq!(read!(a).length0(), int!(0));
        assert_eq!(read!(a).length1(), int!(0));
        assert_eq!(read!(a).length2(), int!(4));
        deallocate(a);
    }

    struct ClassWrapper<T> {
        /*var*/ t: T,
        /*var*/ x: crate::DafnyInt,
        /*const*/ next: *mut ClassWrapper<T>,
        /*const*/ constant: crate::DafnyInt,
    }
    impl<T> AsAny for ClassWrapper<T>
    where
        T: 'static,
    {
        fn as_any(&self) -> &dyn Any {
            self
        }
        fn as_any_mut(&mut self) -> &mut dyn Any {
            self
        }
    }
    impl<T: Clone> ClassWrapper<T> {
        fn constant_plus_x(&self) -> crate::DafnyInt {
            self.constant.clone() + self.x.clone()
        }
        fn increment_x(&mut self) {
            self.x = self.x.clone() + int!(1);
        }
    }

    impl<T: Clone + Display> ClassWrapper<T> {
        fn constructor(t: T) -> *mut ClassWrapper<T> {
            let this = crate::allocate::<ClassWrapper<T>>();
            update_field_nodrop!(this, t, t);
            update_field_nodrop!(this, next, this);
            // If x is assigned twice, we need to keep track of whether it's assigned
            // like in methods.
            let mut x_assigned = false;
            update_field_uninit!(this, x, x_assigned, int!(2));
            update_field_uninit!(this, x, x_assigned, int!(1));
            // If we can prove that x is assigned, we can even write this
            modify!(this).x = int!(0);
            update_field_nodrop!(this, constant, int!(42));
            this
        }
    }

    #[test]
    #[allow(unused_unsafe)]
    fn test_class_wrapper() {
        let c: *mut ClassWrapper<i32> = ClassWrapper::constructor(53);
        assert_eq!(read!(c).constant, int!(42));
        assert_eq!(read!(c).t, 53);
        assert_eq!(read!(c).x, int!(0));
        assert_eq!(read!(read!(c).next).t, 53);
        assert_eq!(read!(c).constant_plus_x(), int!(42));
        modify!(c).increment_x();
        assert_eq!(read!(c).constant_plus_x(), int!(43));
        modify!(c).x = int!(40);
        assert_eq!(read!(c).constant_plus_x(), int!(82));
        modify!(c).t = 54;
        assert_eq!(read!(c).t, 54);
        let x_copy = read!(c).x.clone();
        assert_eq!(Rc::strong_count(&x_copy.data), 2);
        deallocate(c);
        assert_eq!(Rc::strong_count(&x_copy.data), 1);
    }

    #[test]
    #[allow(unused_unsafe)]
    fn test_extern_class_wrapper_with_box() {
        #[allow(unused_mut)]
        let mut c = Box::new(ClassWrapper {
            t: 53,
            x: int!(0),
            next: std::ptr::null_mut(),
            constant: int!(42),
        });
        assert_eq!(read!(c).constant, int!(42));
        modify!(c).increment_x();
        assert_eq!(read!(c).constant_plus_x(), int!(43));
        // Automatically dropped
    }

    #[test]
    #[allow(unused_unsafe)]
    fn test_extern_class_wrapper_with_mutable_borrow() {
        #[allow(unused_mut)]
        let c: &mut ClassWrapper<i32> = &mut ClassWrapper {
            t: 53,
            x: int!(0),
            next: std::ptr::null_mut(),
            constant: int!(42),
        };
        assert_eq!(read!(c).constant, int!(42));
        modify!(c).increment_x();
        assert_eq!(read!(c).constant_plus_x(), int!(43));
        // Automatically dropped
    }

    // Requires test1 || test2
    // We will not do that as it enables the compiler to assume that t contains a valid Rc<i32> when it does not.
    // Prefer MaybePlacebo
    fn assign_lazy_in_method(test1: bool, test2: bool) -> Rc<i32> {
        let mut t = MaybePlacebo::<Rc<i32>>::new();
        if test1 {
            t = MaybePlacebo::from(Rc::new(5 as i32));
        }
        if test2 {
            t = MaybePlacebo::from(Rc::new(
                7 as i32 + if test1 { *MaybePlacebo::read(&t) } else { 0 },
            ));
        }
        println!("{}", MaybePlacebo::read(&t));
        MaybePlacebo::read(&t)
    }

    #[test]
    fn assign_lazy_in_method_test() {
        let mut t = assign_lazy_in_method(true, false);
        assert_eq!(*t, 5);
        t = assign_lazy_in_method(false, true);
        assert_eq!(*t, 7);
        t = assign_lazy_in_method(true, true);
        assert_eq!(*t, 12);
    }

    fn override_placebo<T: Clone>(o: T, do_override: bool) {
        let mut x: MaybePlacebo<T> = MaybePlacebo::<T>::new();
        if do_override {
            x = MaybePlacebo::from(o.clone());
        }
    }

    #[test]
    fn test_placebo() {
        override_placebo::<Rc<BigInt>>(Rc::new(BigInt::from(1)), false);
        override_placebo::<Rc<BigInt>>(Rc::new(BigInt::from(1)), true);
        override_placebo::<DafnyInt>(int!(1), false);
        override_placebo::<DafnyInt>(int!(1), true);
        let _x: MaybePlacebo<*mut ClassWrapper<DafnyInt>> =
            MaybePlacebo::<*mut ClassWrapper<DafnyInt>>::new();
        //let mut f: Rc<dyn Fn(Class) -> Class> = <Rc<dyn Fn(Class) -> Class> as Placebo>::new();
    }

    #[test]
    fn test_maybe_placebos_from() {
        let x = (1, 2, 3, 4);
        let (a, b, c, d) = maybe_placebos_from!(x, 0, 1, 2, 3);
        assert_eq!(a.read(), 1);
        assert_eq!(b.read(), 2);
        assert_eq!(c.read(), 3);
        assert_eq!(d.read(), 4);
    }

    #[test]
    fn test_coercion_immutable() {
        let o = ClassWrapper::<i32>::constructor(1);
        let a = UpcastTo::<*mut dyn Any>::upcast_to(o);
        assert_eq!(cast!(a, ClassWrapper<i32>), o);
        let seq_o = seq![o];
        let seq_a = UpcastTo::<Sequence<*mut dyn Any>>::upcast_to(seq_o);
        assert_eq!(cast!(seq_a.get_usize(0), ClassWrapper<i32>), o);
        let set_o = set! {o};
        let set_a = UpcastTo::<Set<*mut dyn Any>>::upcast_to(set_o);
        assert_eq!(cast!(set_a.peek(), ClassWrapper<i32>), o);
        let multiset_o = multiset! {o, o};
        let multiset_a = UpcastTo::<Multiset<*mut dyn Any>>::upcast_to(multiset_o);
        assert_eq!(cast!(multiset_a.peek(), ClassWrapper<i32>), o);
        let map_o = map![1 => o, 2 => o];
        let map_a = UpcastTo::<Map<i32, *mut dyn Any>>::upcast_to(map_o);
        assert_eq!(cast!(map_a.get(&1), ClassWrapper<i32>), o);
    }

    #[test]
    fn test_defaults() {
        let set_i32 = <Set<i32> as Default>::default();
        let seq_i32 = <Sequence<i32> as Default>::default();
        let map_i32 = <Map<i32, i32> as Default>::default();
        let multiset_i32 = <Multiset<i32> as Default>::default();
        assert_eq!(set_i32.cardinality_usize(), 0);
        assert_eq!(seq_i32.cardinality_usize(), 0);
        assert_eq!(map_i32.cardinality_usize(), 0);
        assert_eq!(multiset_i32.cardinality_usize(), 0);
    }

    #[test]
    fn test_nontrivial_defaults() {
        let set_i32 = <Set<i32> as NontrivialDefault>::nontrivial_default();
        let seq_i32 = <Sequence<i32> as NontrivialDefault>::nontrivial_default();
        let map_i32 = <Map<i32, i32> as NontrivialDefault>::nontrivial_default();
        let multiset_i32 = <Multiset<i32> as NontrivialDefault>::nontrivial_default();
        assert_eq!(set_i32.cardinality_usize(), 0);
        assert_eq!(seq_i32.cardinality_usize(), 0);
        assert_eq!(map_i32.cardinality_usize(), 0);
        assert_eq!(multiset_i32.cardinality_usize(), 0);
        let ptr_i32 = <*mut i32 as NontrivialDefault>::nontrivial_default();
        assert_eq!(ptr_i32, std::ptr::null_mut());
    }

    #[test]
    fn test_function_wrappers() {
        let f: Rc<dyn Fn(i32) -> i32> = Rc::new(|i: i32| i + 1);
        let g = f.clone();
        let _h = seq![g];
    }

    #[test]
    fn test_forall_exists() {
        assert!(integer_range(int!(0), int!(10))
            .all(Rc::new(|i: DafnyInt| i.clone() < int!(10)).as_ref()));
        assert!(!integer_range(int!(0), int!(11))
            .all(Rc::new(|i: DafnyInt| i.clone() < int!(10)).as_ref()));
        assert!(!integer_range(int!(0), int!(10))
            .any(Rc::new(|i: DafnyInt| i.clone() >= int!(10)).as_ref()));
        assert!(integer_range(int!(0), int!(11))
            .any(Rc::new(|i: DafnyInt| i.clone() >= int!(10)).as_ref()));

        assert!(integer_range(int!(0), int!(10)).all(
            Rc::new(|i: DafnyInt| !(i.clone() % int!(4) == int!(0))
                || i.clone() < int!(10) && i.clone() % int!(2) == int!(0))
            .as_ref()
        ));
        assert!(integer_range(int!(0), int!(11)).all(
            Rc::new(|i: DafnyInt| !(i.clone() % int!(4) == int!(0))
                || i.clone() < int!(10) && i.clone() % int!(2) == int!(0))
            .as_ref()
        ));
        assert!(!integer_range(int!(0), int!(10)).any(
            Rc::new(|i: DafnyInt| i.clone() % int!(4) == int!(0)
                && i.clone() >= int!(10)
                && i.clone() % int!(2) == int!(0))
            .as_ref()
        ));
        assert!(!integer_range(int!(0), int!(11)).any(
            Rc::new(|i: DafnyInt| i.clone() % int!(4) == int!(0)
                && i.clone() >= int!(10)
                && i.clone() % int!(2) == int!(0))
            .as_ref()
        ));

        assert!(exact_range(10).all(Rc::new(|i: i32| i == 10).as_ref()));
        assert!(exact_range(10).any(Rc::new(|i: i32| i == 10).as_ref()));
        assert!(!exact_range(10).all(Rc::new(|i: i32| i != 10).as_ref()));
        assert!(!exact_range(10).any(Rc::new(|i: i32| i != 10).as_ref()));

        assert!(seq![1, 3, 5, 7]
            .iter()
            .all(Rc::new(|i: u32| i % 2 == 1).as_ref()));
        assert!(!seq![1, 3, 5, 7]
            .iter()
            .any(Rc::new(|i: u32| i % 2 == 0).as_ref()));
        assert!(!seq![1, 3, 5, 7, 8]
            .iter()
            .all(Rc::new(|i: u32| i % 2 == 1).as_ref()));
        assert!(seq![1, 3, 5, 7, 8]
            .iter()
            .any(Rc::new(|i: u32| i % 2 == 0).as_ref()));

        assert!(set! {1, 3, 5, 7}
            .iter()
            .cloned()
            .all(Rc::new(|i: u32| i % 2 == 1).as_ref()));
        assert!(!set! {1, 3, 5, 7}
            .iter()
            .cloned()
            .any(Rc::new(|i: u32| i % 2 == 0).as_ref()));
        assert!(!set! {1, 3, 5, 7, 8}
            .iter()
            .cloned()
            .all(Rc::new(|i: u32| i % 2 == 1).as_ref()));
        assert!(set! {1, 3, 5, 7, 8}
            .iter()
            .cloned()
            .any(Rc::new(|i: u32| i % 2 == 0).as_ref()));

        for i in set! {1, 3, 5, 7}.iter() {
            println!("{}", i);
        }

        assert!(multiset! {1, 1, 5, 7}
            .iter()
            .all(Rc::new(|i: u32| i % 2 == 1).as_ref()));
        assert!(!multiset! {1, 1, 5, 7}
            .iter()
            .any(Rc::new(|i: u32| i % 2 == 0).as_ref()));
        assert!(!multiset! {1, 1, 5, 7, 8}
            .iter()
            .all(Rc::new(|i: u32| i % 2 == 1).as_ref()));
        assert!(multiset! {1, 1, 5, 7, 8}
            .iter()
            .any(Rc::new(|i: u32| i % 2 == 0).as_ref()));

        let m = map![1 => 4, 3 => 6, 5 => 8];
        let m2 = m.clone();
        let m3 = m.clone();
        assert!(m
            .clone()
            .iter()
            .all(Rc::new(move |i: u32| i + 3 == m2.get(&i)).as_ref()));
        assert!(!m
            .iter()
            .any(Rc::new(move |i: u32| i + 2 == m3.get(&i)).as_ref()));
        let m = map![1 => 4, 3 => 7, 5 => 7];
        let m2 = m.clone();
        let m3 = m.clone();
        assert!(!m
            .clone()
            .iter()
            .all(Rc::new(move |i: u32| i + 3 == m2.get(&i)).as_ref()));
        assert!(m
            .iter()
            .any(Rc::new(move |i: u32| i + 2 == m3.get(&i)).as_ref()));
    }

    #[test]
    fn test_for_loops() {
        let mut sum: i32 = 0;
        for i in integer_range(1, 11) {
            sum += i;
        }
        assert_eq!(sum, 55);

        let mut sum: i32 = 0;
        for i in integer_range_down(11, 1) {
            sum += i;
        }
        assert_eq!(sum, 55);

        let mut sum: i32 = 0;
        for i in integer_range_unbounded(1) {
            sum += i;
            if i == 10 {
                break;
            }
        }
        assert_eq!(sum, 55);

        let mut sum: i32 = 0;
        for i in integer_range_down_unbounded(11) {
            sum += i;
            if i == 1 {
                break;
            }
        }
        assert_eq!(sum, 55);
    }

    trait NodeRcMutTrait: AsAny {}

    pub struct NodeRcMut {
        val: DafnyInt,
        next: Object<NodeRcMut>,
    }
    impl AsAny for NodeRcMut {
        fn as_any(&self) -> &dyn Any {
            self
        }
        fn as_any_mut(&mut self) -> &mut dyn Any {
            self
        }
    }
    impl NodeRcMut {
        fn _ctor(this: Object<NodeRcMut>, val: DafnyInt) {
            let mut val_assign = false;
            let mut next_assign = false;
            update_field_uninit_rcmut!(this.clone(), val, val_assign, val);
            update_field_if_uninit_rcmut!(this.clone(), next, next_assign, Object(None));
        }
    }
    impl NodeRcMutTrait for NodeRcMut {}

    #[test]
    fn test_rcmut() {
        let x: Object<NodeRcMut> = allocate_rcmut::<NodeRcMut>();
        NodeRcMut::_ctor(x.clone(), int!(42));
        assert_eq!(refcount!(x.clone()), 2);
        assert_eq!(rd!(x.clone()).val, int!(42));
        md!(x.clone()).next = x.clone();
        assert_eq!(refcount!(x.clone()), 3);
        assert_eq!(rd!(rd!(x.clone()).next.clone()).val, int!(42));
        md!(rd!(x.clone()).next.clone()).next = Object(None);
        assert_eq!(refcount!(x.clone()), 2);
        let y: Object<dyn Any> = x.clone().upcast_to();
        assert_eq!(refcount!(x.clone()), 3);
        let z: Object<dyn NodeRcMutTrait> = x.clone().upcast_to();
        assert_eq!(refcount!(x.clone()), 4);
        let a2: Object<NodeRcMut> = cast_object!(y.clone(), NodeRcMut);
        assert_eq!(refcount!(x.clone()), 5);
        assert_eq!(rd!(a2.clone()).val, int!(42));
        let a3: Object<NodeRcMut> = cast_object!(z.clone(), NodeRcMut);
        assert_eq!(refcount!(x.clone()), 6);
        assert_eq!(rd!(a3.clone()).val, int!(42));
        
        let a: Object<[i32]> = rcmut::array_from_rc(Rc::new([42, 43, 44]));
        assert_eq!(rd!(a.clone()).len(), 3);
        assert_eq!(rd!(a.clone())[0], 42);
        assert_eq!(rd!(a.clone())[1], 43);
        assert_eq!(rd!(a.clone())[2], 44);
        let b = a.clone();
        md!(b.clone())[0] = 45;
        assert_eq!(rd!(a.clone())[0], 45);
    }

    pub struct NodeRawMut {
        val: DafnyInt,
        next: *mut NodeRawMut,
    }
    impl NodeRawMut {
        fn _ctor(this: *mut NodeRawMut, val: DafnyInt) {
            let mut val_assign = false;
            update_field_uninit!(this, val, val_assign, val);
        }
    }
    impl AsAny for NodeRawMut {
        fn as_any(&self) -> &dyn Any {
            self
        }
        fn as_any_mut(&mut self) -> &mut dyn Any {
            self
        }
    }
    impl NodeRcMutTrait for NodeRawMut {}
    
    UpcastTo!(NodeRawMut, dyn NodeRcMutTrait);

    #[test]
    fn test_rawmut() {
        let x: *mut NodeRawMut = allocate::<NodeRawMut>();
        NodeRawMut::_ctor(x.clone(), int!(42));
        //assert_eq!(refcount!(x.clone()), 2);
        assert_eq!(read!(x.clone()).val, int!(42));
        modify!(x.clone()).next = x.clone();
        //assert_eq!(refcount!(x.clone()), 3);
        assert_eq!(read!(read!(x.clone()).next.clone()).val, int!(42));
        modify!(read!(x.clone()).next.clone()).next = std::ptr::null_mut();
        //assert_eq!(refcount!(x.clone()), 2);
        let y = x.upcast_to();
        let z: *mut dyn NodeRcMutTrait = modify!(x).upcast_to();
        let a2: *mut NodeRawMut = cast!(y, NodeRawMut);
        let a3: *mut NodeRawMut = cast!(z, NodeRawMut);
        //assert_eq!(refcount!(x.clone()), 3);
        deallocate(x);

        let a = array::from_native(Box::new([42, 43, 44]));
        assert_eq!(read!(a.clone()).len(), 3);
        assert_eq!(read!(a.clone())[0], 42);
        assert_eq!(read!(a.clone())[1], 43);
        assert_eq!(read!(a.clone())[2], 44);
        let b = a.clone();
        modify!(b.clone())[0] = 45;
        assert_eq!(read!(a.clone())[0], 45);
    }
}
