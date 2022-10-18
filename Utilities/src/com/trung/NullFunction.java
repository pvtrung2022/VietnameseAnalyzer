package com.trung;

@FunctionalInterface
public interface NullFunction<T>
{
    public T apply();

    public static <T> NullFunction<T> createInstance(NullFunction<T> func)
    {
        return func;
    }
}
