package IJ_Trails.src.main.java;/*
 * Copyright (c) 2013, Graeme Ball
 * Micron Oxford, University of Oxford, Department of Biochemistry.
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
 *  along with this program.  If not, see http://www.gnu.org/licenses/ .
 */

import ij.IJ;
import ij.ImageJ;
import ij.ImagePlus;
import ij.ImageStack;
import ij.gui.GenericDialog;
import ij.plugin.PlugIn;
import ij.process.ImageProcessor;
import ij.process.FloatProcessor;

/**
 * Trail/average intensities over a time window for an imp sequence.
 *
 * @author graemeball@googlemail.com
 */
public class Trails_ implements PlugIn {

    // ImagePlus and properties
    ImagePlus imp;
    int width;
    int height;
    int nc;
    int nz;
    int nt;

    // plugin parameters with defaults
    public int twh = 2;     // time window half-width for trails

    public void run(String arg) {
        ImagePlus imp = IJ.getImage();
        if (showDialog()) {
            if (imp.getNFrames() > (2 * twh + 1)) {
                ImagePlus imResult = exec(imp);
                imResult.show();
            } else {
                IJ.showMessage("Insufficient time points, " + nt);
            }
        }
    }

    boolean showDialog() {
        GenericDialog gd = new GenericDialog("Trails");
        gd.addNumericField("time_window half-width", twh, 0);
        gd.showDialog();
        if (gd.wasCanceled())
            return false;
        twh = (int)gd.getNextNumber();
        return true;
    }

    /**
     * Execute time-averaging, returning trailed ImagePlus.
     * Builds array of pixel arrays for sliding window of time frames.
     *
     * @param imp (multi-dimensional, i.e. multiple frames)
     */
    public ImagePlus exec(ImagePlus imp) {
        this.nt = imp.getNFrames();
        this.nz = imp.getNSlices();
        this.nc = imp.getNChannels();
        this.width = imp.getWidth();
        this.height = imp.getHeight();
        ImageStack inStack = imp.getStack();
        int size = inStack.getSize();
        ImageStack outStack = new ImageStack(width, height, size);

        // for all channels and slices, process sliding time window
        for (int c = 1; c <= nc; c++) {
            for (int z = 1; z <= nz; z++) {
                // build initial time window array of pixel arrays
                float[][] tWinPix = new float[2 * twh + 1][width * height];
                int wmin = 0;  // window min index
                int wcurr = 0;  // index within window of current frame
                int wmax = twh;  // window max index
                for (int t = 1; t <= wmax + 1; t++) {
                    int index = imp.getStackIndex(c, z, t);
                    tWinPix[t-1] = getfPixels(inStack, index);
                }
                // process each t and update sliding time window
                for (int t = 1; t <= nt; t++) {
                    float[] fgPix = trail(tWinPix, wcurr, wmin, wmax);
                    FloatProcessor fp2 =
                            new FloatProcessor(width, height, fgPix);
                    int index = imp.getStackIndex(c, z, t);
                    outStack.addSlice("" + index, (ImageProcessor)fp2, index);
                    outStack.deleteSlice(index);  // addSlice() *inserts*
                    // sliding window update for next t
                    if (t > twh) {
                        // remove old pixel array from start
                        tWinPix = rmFirst(tWinPix, wmax);
                    } else {
                        wcurr += 1;
                        wmax += 1;
                    }
                    if (t < nt - twh) {
                        // append new pixel array (frame t+twh) to end
                        int newPixIndex = imp.getStackIndex(c, z, t + twh + 1);
                        tWinPix[wmax] = getfPixels(inStack, newPixIndex);
                    } else {
                        wmax -= 1;
                    }
                }
            }
        }
        ImagePlus result = new ImagePlus("Trail" + Integer.toString(2 * twh + 1)
                + "_" + imp.getTitle(), outStack);
        result.setDimensions(nc, nz, nt);
        result.setOpenAsHyperStack(true);
        return result;
    }

    /**
     * Return a float array of pixels for a given stack slice.
     */
    final float[] getfPixels(ImageStack stack, int index) {
        ImageProcessor ip = stack.getProcessor(index);
        FloatProcessor fp = (FloatProcessor)ip.convertToFloat();
        float[] pix = (float[])fp.getPixels();
        return pix;
    }

    /** Trail tCurr pixels using tWinPix time window. */
    final float[] trail(float[][] tWinPix, int wcurr, int wmin, int wmax) {
        int numPix = width*height;
        float[] tPix = new float[numPix];
        for (int v=0; v<numPix; v++) {
            float[] tvec = getTvec(tWinPix, v, wmin, wmax);
            tPix[v] = mean(tvec);
        }
        return tPix;
    }

    /** Build time vector for this pixel for  given window. */
    final float[] getTvec(float[][] tWinPix, int v, int wmin, int wmax) {
        float[] tvec = new float[wmax - wmin + 1];
        for (int w=wmin; w<=wmax; w++) {
            tvec[w] = tWinPix[w][v];  // time window vector for a pixel
        }
        return tvec;
    }

    /** Calculate mean of array of floats. */
    final float mean(float[] tvec) {
        float mean = 0;
        for (int t=0; t<tvec.length; t++) {
            mean += tvec[t];
        }
        return mean / tvec.length;
    }

    /** Remove first array of pixels and shift the others to the left. */
    final float[][] rmFirst(float[][] tWinPix, int wmax) {
        for (int i=0; i < wmax; i++) {
            tWinPix[i] = tWinPix[i+1];
        }
        return tWinPix;
    }

    public void showAbout() {
        IJ.showMessage("Trails",
            "Trail/average intensities over a given time window."
        );
    }

    /** Main method for testing. */
    public static void main(String[] args) {
        Class<?> clazz = Trails_.class;
        new ImageJ();
        // open TrackMate FakeTracks test data from the Fiji wiki
        ImagePlus image = IJ.openImage(
                "http://fiji.sc/tinevez/TrackMate/FakeTracks.tif");
        image.show();
        IJ.runPlugIn(clazz.getName(), "");
    }
}