package com.trung;

@FunctionalInterface
public interface TernaryFunction<S, T, Q, R>
{
    public R apply(S s, T t, Q q);
}
