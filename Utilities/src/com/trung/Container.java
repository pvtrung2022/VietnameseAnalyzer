package com.trung;

import java.util.HashMap;
import java.util.HashSet;

/**
 * lớp này dùng để chứa các phần tử và có thêm các phần tử và các phần tử được gọi lại
 * bởi các id
 */
public class Container
{
    private int index = -1;
    private HashMap<Integer, Object> container=new HashMap<>();

    public void clear()
    {
        this.container.clear();
        this.index = -1;
    }

    public int add(Object ele)
    {
        index++;
        this.container.put(index, ele);
        return index;
    }

    public Object get(int id)
    {
        return this.container.get(id);
    }

}
