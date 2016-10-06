#include "lean_runtime.h"

// Take the inductive type that Lean uses to represent a character
// and convert it to a raw character.
char lean_char_to_raw_char(lean::obj c) {
    char r = (c[0].cidx() << 7) |
             (c[1].cidx() << 6) |
             (c[2].cidx() << 5) |
             (c[3].cidx() << 4) |
             (c[4].cidx() << 3) |
             (c[5].cidx()<< 2) |
             (c[6].cidx() << 1) |
             (c[7].cidx());
    return r;
}

// Take the inductive type that Lean uses to represent a string
// and convert it to a raw character.
lean::obj string_to_raw_string(lean::obj rw, lean::obj string) {
    std::string *raw_string = new std::string;
    auto cursor = string;
    while (cursor.cidx() == 1) {
        *raw_string += lean_char_to_raw_char(cursor[0]);
        cursor = cursor[1];
    }
    auto rs = lean::mk_raw_ptr((void*)raw_string->c_str());
    return lean::mk_obj(0, { rw, rw, rw, rs });
}

lean::obj raw_print(lean::obj rw, lean::obj rs) {
    auto unit = lean::mk_obj(0);
    auto ptr = (char *)rs.raw_ptr();
    std::cout << ptr;
    return lean::mk_obj(0, { rw, rw, rw, unit });
}
