import init.meta.expr

-- builtin stuff
meta constant native.is_internal_cnstr : expr → option unsigned
meta constant native.is_internal_cases : expr → option unsigned
meta constant native.is_internal_proj : expr → option unsigned
meta constant native.get_nat_value : expr → option nat
