package com.trung;

import java.util.HashMap;

public class ProgressIndicator
{
    private String indexVariable = null;
    private double xMin = -1;
    private double xMax = -1;
    public boolean Stopped = true;
    private long delay = 0;
    private Long currentTime = null;

    public void setDelay(long time)
    {
        this.delay = time;
    }

    public void show()
    {
        Stopped = false;
        var code = "PrintTemporary[{{ProgressIndicator[Dynamic@indexVariable,{xMin,xMax}],Button[\"Stop\",%0@Stopped=True,ImageSize->{80,Automatic}]}}//Grid]";
        var rule = new HashMap<String, String>();
        rule.put("indexVariable", indexVariable);
        rule.put("xMin", Double.toString(xMin));
        rule.put("xMax", Double.toString(xMax));
        code = Utilities.stringReplace(code, rule);
        Utilities.executeMathematicaCode(code, this);
    }

    public void setValue(double value)
    {
        NullAction action = () ->
        {
            var code = indexVariable + "=" + Double.toString(value);
            Utilities.executeMathematicaCode(code);
        };
        if (this.currentTime == null)
        {
            action.apply();
            this.currentTime = System.currentTimeMillis();
            return;
        } else
        {
            var auxTime = System.currentTimeMillis();
            if (auxTime - this.currentTime.doubleValue() > this.delay)
            {
                action.apply();
                this.currentTime = System.currentTimeMillis();
            }
        }
    }

    public ProgressIndicator(double min, double max)
    {
        this.xMin = min;
        this.xMax = max;
        var aux = Utilities.executeMathematicaCode("Unique@i");
        indexVariable = aux.toString();
        var code = indexVariable + "=" + Double.toString(min);
        Utilities.executeMathematicaCode(code);
    }
}
