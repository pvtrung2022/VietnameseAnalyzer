package com.trung;

@FunctionalInterface
public interface UnaryFunction<S,T>
{
    public T apply(S s);
}
