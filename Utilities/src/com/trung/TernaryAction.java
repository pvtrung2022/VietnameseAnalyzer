package com.trung;

@FunctionalInterface
public interface TernaryAction<S,T,Q>
{
    public void apply(S s,T t,Q q);
}
