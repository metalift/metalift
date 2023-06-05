package original.stats;

/**
 *   PlotUtil.java
 *  ==============
 *
 *  Copyright (C) 2013-2014  Magdalen Berns <m.berns@sms.ed.ac.uk>
 * 
 *  This program is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program.  If not, see <http://www.gnu.org/licenses/>.
*/

import java.util.Scanner;


public class PlotReader{

    public static double[] data1Column(Scanner scan, int length){
        double[] data=new double[length];
        for (int i=0;i<data.length;i++) data[i] = IOUtil.skipToDouble(scan);
        return data;
    }

    //Initialise the array with the values from a file
    public static double[][] data2Column(Scanner scan, int length){
        double[][] data = new double[length][2];
        for (int i=0;i<data.length;i++){
            for (int j=0;j<data[0].length;j++){
                data[i][j] = (float) IOUtil.skipToDouble(scan);
            }
        }
        return data;
    }

    //Initialise the array with the values from a file
    public static double[][] data3Column(Scanner scan, int length){
        double[][] data = new double[length][3];
        for (int i=0;i<data.length;i++){
            for (int j=0;j<data[0].length;j++)data[i][j] = (float) IOUtil.skipToDouble(scan);
        }
        return data;
    }

    //Initialise the array with the values from a file
    public static double[][] data4Column(Scanner scan, int length){
        double[][] data = new double[length][4];
        for (int i=0;i<data.length;i++){
            for (int j=0;j<data[0].length;j++) data[i][j] = (float) IOUtil.skipToDouble(scan);
        }
        return data;
    }
}