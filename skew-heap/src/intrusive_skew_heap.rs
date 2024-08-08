use std::{
    mem::{offset_of, swap},
    ptr::null_mut,
};

#[derive(Debug)]
pub struct Hook {
    parent: *mut Hook,
    left: *mut Hook,
    right: *mut Hook,
}

#[derive(Debug)]
pub struct Entry {
    x: i64,

    parent: *mut Entry,
    left: *mut Entry,
    right: *mut Entry,
}

impl Entry {
    pub fn new(x: i64) -> Entry {
        Entry {
            x,
            parent: std::ptr::null_mut(),
            left: std::ptr::null_mut(),
            right: std::ptr::null_mut(),
        }
    }
}

pub fn meld(mut a: *mut Entry, mut b: *mut Entry, parent: *mut Entry) -> *mut Entry {
    if a.is_null() {
        if b.is_null() {
            return null_mut();
        }
        unsafe { (*b).parent = parent };
        return b;
    }
    if b.is_null() {
        unsafe { (*a).parent = parent };
        return a;
    }
    unsafe {
        if (*a).x > (*b).x {
            swap(&mut a, &mut b);
        }
        (*a).right = meld((*a).right, b, a);
        swap(&mut (*a).left, &mut (*a).right);
        (*a).parent = parent;
    }
    a
}

pub unsafe fn meld_hook<Entry: Ord, const OFFSET: usize>(
    mut a: *mut Hook,
    mut b: *mut Hook,
    parent: *mut Hook,
) -> *mut Hook {
    if a.is_null() {
        if b.is_null() {
            return null_mut();
        }
        unsafe { (*b).parent = parent };
        return b;
    }
    if b.is_null() {
        unsafe { (*a).parent = parent };
        return a;
    }
    unsafe {
        let entry_a = a.byte_sub(OFFSET) as *const Entry;
        let entry_b = b.byte_sub(OFFSET) as *const Entry;
        if entry_a > entry_b {
            swap(&mut a, &mut b);
        }
        (*a).right = meld_hook::<Entry, OFFSET>((*a).right, b, a);
        swap(&mut (*a).left, &mut (*a).right);
        (*a).parent = parent;
    }
    a
}

// Pushes a new element into the heap and returns the new root
pub fn push(root: *mut Entry, new_entry: *mut Entry) -> *mut Entry {
    meld(root, new_entry, null_mut())
}

// Returns the new root and the removed minimum element
pub fn pop_min(root: *mut Entry) -> (*mut Entry, *mut Entry) {
    if root.is_null() {
        return (null_mut(), null_mut());
    }
    let new_root = meld(
        unsafe { (*root).left },
        unsafe { (*root).right },
        null_mut(),
    );
    unsafe {
        (*root).left = null_mut();
        (*root).right = null_mut();
        (*root).parent = null_mut();
    }
    (new_root, root)
}

// Unlinks the entry from the heap and returns new root
pub fn unlink(root: *mut Entry, entry: *mut Entry) -> *mut Entry {
    // If the entry is the root, just pop it
    if entry == root {
        let (new_root, _) = pop_min(root);
        return new_root;
    }
    assert_ne!(unsafe { (*entry).parent }, null_mut());

    let subtree = meld(
        unsafe { (*entry).left },
        unsafe { (*entry).right },
        unsafe { (*entry).parent },
    );
    // Replace the link from the parent node to the entry with the subtree
    unsafe {
        if (*(*entry).parent).left == entry {
            (*(*entry).parent).left = subtree;
        } else {
            (*(*entry).parent).right = subtree;
        }
    }
    // Clear the links from the entry
    unsafe {
        (*entry).left = null_mut();
        (*entry).right = null_mut();
        (*entry).parent = null_mut();
    }
    // The root of the heap does not change, so return it as is
    root
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_skew_heap() {
        use super::{pop_min, push, unlink, Entry};
        let mut root = std::ptr::null_mut();
        let mut entries = vec![];
        for i in 0..10 {
            let mut entry = Box::new(Entry::new(i));
            root = push(root, entry.as_mut() as *mut Entry);
            entries.push(entry);
        }
        /*
        for entry in entries.iter() {
            let (new_root, min_entry) = pop_min(root);
            assert_eq!(unsafe { (*min_entry).x }, unsafe { (**entry).x });
            root = new_root;
        }
        */
        for mut entry in entries {
            root = unlink(root, entry.as_mut() as *mut Entry);
        }
        assert!(root.is_null());
    }
}
