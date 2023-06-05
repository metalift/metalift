package original.stats;

/*
    PlotWriter.java
    =============
    
    This is a utility for plotting
    Takes various input files and manipulates to output a different kind of plot. 
    For writing files so they can be plotted using pgfplots or similar
	Currently a little less of a mess. Starting to think this should be instances 
    Copyright (C) 2013  Magdalen Berns
    
    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
*/

import java.io.PrintWriter;

public class PlotWriter{

 
    public static void write(double[] x, double[] y, PrintWriter fileOut){
        for(int i=0; i<y.length;i++){
            fileOut.printf("%2.5f %2.5f", x[i],y[i]);
            fileOut.println();
        }
    }
    public static void write(double[][] data, PrintWriter fileOut){
        for(int i=0; i<data.length;i++){
            fileOut.printf("%2.5f %2.5f", data[i][0], data[i][1]);
            fileOut.println();
        }
    }
        //Will write to file all needed columns 
    public static void errors(double[] x, double[] y, double xError, double[] yError, PrintWriter fileOut){
        for(int i=0; i<x.length;i++){
            fileOut.printf("%2.5f %2.5f %2.5f %2.5f ", x[i], y[i], xError,yError[i]);
            fileOut.println();
        }
    }
    //Will write to file all needed columns 
   public static void errorsFit(double[] x, double[] y, double[] fit, double xError, double[] yError, PrintWriter fileOut){
      for(int i=0; i<y.length;i++){
        fileOut.printf("%2.5f %2.5f %2.5f %2.5f %2.5f", x[i], y[i], fit[i], xError,yError[i]);
        fileOut.println();
      }         
    }
   public static void aColumn(double[] n, PrintWriter fileOut){
        for(int i=0; i<n.length;i++){
            fileOut.printf("%2.5f ", n[i]);
            fileOut.println();
        }
    }
    public static void calibrate(double[] x, double[] y, PrintWriter fileOut, double[] amount){
        double[] calibrate = new double[x.length];
        for(int i=0; i<y.length;i++){
            System.out.println(amount[i]);
            calibrate[i]+= x[i]-amount[i];

            fileOut.printf("%2.2f %2.2f",calibrate[i] ,y[i]);
            fileOut.println();
        }
    }
    public static void peaksUp(double[][] data, PrintWriter upFile, double minValue){
    
        double largeUp=0.0;

        for(int i=0; i<data.length-1; i++){

            //Check that there has been an initial increase
            if(data[i][1]>data[0][1]){

                //if so check that it's significant
                if(data[i][1]>largeUp && data[i][1] > minValue){
                
                    largeUp = data[i][1];
                    System.out.printf("%2.2f ",data[i][0]);
                    upFile.printf("%2.2f %2.2f ",data[i][0], largeUp);
                    upFile.println();
                }
            }
        }
        System.out.println();
	}
}