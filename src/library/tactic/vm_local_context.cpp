/* Copyright 2019 E.W.Ayers */
#include "library/local_context.h"
#include "library/vm/vm.h"
#include "library/vm/vm_name.h"
#include "library/vm/vm_expr.h"
#include "library/vm/vm_option.h"
namespace lean {
struct vm_local_context : public vm_external {
    local_context m_val;
    vm_local_context(local_context const & v): m_val(v) {}
    virtual ~vm_local_context() {}
    virtual void dealloc() override { this->~vm_local_context(); get_vm_allocator().deallocate(sizeof(vm_local_context), this);}
    virtual vm_external * ts_clone(vm_clone_fn const &) override { return new vm_local_context(m_val); }
    virtual vm_external * clone(vm_clone_fn const &) override { return new (get_vm_allocator().allocate(sizeof(vm_local_context))) vm_local_context(m_val); }
};
vm_obj to_obj(local_context const & lc) {
    return mk_vm_external(new(get_vm_allocator().allocate(sizeof(vm_local_context))) vm_local_context(lc));
}
local_context to_local_context(vm_obj const & o) {
    lean_vm_check(dynamic_cast<vm_local_context*>(to_external(o)));
    return static_cast<vm_local_context*>(to_external(o))->m_val;
}
vm_obj lc_mk_local_decl(vm_obj const & pn, vm_obj const & y, vm_obj const & bi, vm_obj const & lc) {
    local_context lctx = to_local_context(lc);
    expr h = lctx.mk_local_decl(to_name(pn), to_expr(y), to_binder_info(bi));
    return mk_vm_some(mk_vm_pair(to_obj(h), to_obj(lctx)));
}
vm_obj lc_get_local(vm_obj const & n, vm_obj const & lc) {
    local_context const & lctx = to_local_context(lc);
    if (lctx.find_local_decl(to_name(n))) {return mk_vm_none();}
    return mk_vm_some(to_obj(lctx.get_local(to_name(n))));
}
void initialize_vm_local_context() {
    DECLARE_VM_BUILTIN(name({"lc", "mk_local"}), lc_mk_local_decl);
    DECLARE_VM_BUILTIN(name({"lc", "get_local"}), lc_get_local);
}
void finalize_vm_local_context() {
}
}
