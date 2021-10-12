package original.stats;

/*
 * Linearise.java
 * =============
 *
 * This file is a part of a program which serves as a utility for data analysis
 * of experimental data
 *
 * Copyright (C) 2013-2014  Magdalen Berns <m.berns@sms.ed.ac.uk>
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */
import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.Scanner;
import java.io.FileNotFoundException;

public class LinearData{

    public static void main(String[] args) throws IOException {
        String fileName = IOUtil.getFileName();
        Scanner scan = new Scanner(new BufferedReader(new FileReader("files/" + fileName)));
        PrintWriter fitFout = new PrintWriter("files/linear.txt");
        int length = IOUtil.skipToInt(scan);
        double xError=IOUtil.skipToDouble(scan);
        double yError= IOUtil.skipToDouble(scan);
        double[][] data = PlotReader.data2Column(scan, length); 
        PlotUtil p = new PlotUtil(data);
        
        PrintWriter residualsWriter=new PrintWriter("files/residuals.txt");
        handleData(fitFout,residualsWriter, p.x(), p.y(), xError, yError);
    }

    public static void handleData(PrintWriter fitFout,
                                PrintWriter residualsWriter,
                                double[] x,
                                double[] y,
                                double xError,
                                double yError
                                ){
    
        double xMean= StatsUtil.mean(x);
        double yMean= StatsUtil.mean(y);
        
        double xVar= StatsUtil.variance(x, xMean);
        double yVar= StatsUtil.variance(y, yMean);

        double gradient = StatsUtil.gradient(StatsUtil.covariance(xMean,
                                                                  yMean,
                                                                  x,
                                                                  y),
                                            xVar);

        double offset = StatsUtil.yIntercept(xMean,yMean, gradient);
        double[] fit = StatsUtil.fit(x, gradient, offset);
        PlotWriter.errors(x,
                          StatsUtil.residuals(y,fit),
                          xError,
                          Calculate.multiply(y,yError),
                      residualsWriter);
        residualsWriter.close(); 

    	System.out.printf("\nLength of data = %2.0f  ",(float) x.length);
    
        double standardError = StatsUtil.standardError(y, fit);
    	System.out.printf("\nGradient= %2.4f with error +/-  %2.4f ",
    	                  gradient,
    	                  StatsUtil.errorGradient(xVar,standardError, x.length)
    	                 );
    
    	System.out.printf("\nResidual sum squares  = %2.2f ",
    	                  Math.sqrt(standardError / (x.length-1)
    	                  ));
    
    	System.out.printf("\nOffset = %g with error  +/-  %g ",
    	                  offset,
    	                  StatsUtil.errorOffset(x.length,
    	                                        xVar,
    	                                        xMean,
    	                                        standardError)
                         );
    
        System.out.printf("\nLinear Correlation Coefficient %g",
        StatsUtil.linearCorrelationCoefficient(StatsUtil.regressionSumOfSquares(fit, yMean), yVar));
        
        PlotWriter.errorsFit(x,
                         y,
                         fit,
                         xError,
                         Calculate.multiply(y, yError),
                     fitFout);
        fitFout.close();
        
        System.exit(0);
    }
}