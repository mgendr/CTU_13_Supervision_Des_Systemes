#! /usr/bin/env python
#  Copyright (C) 2009  Sebastian Garcia, Martin Grill, Jan Stiborek
#
#  This program is free software; you can redistribute it and/or modify
#  it under the terms of the GNU General Public License as published by
#  the Free Software Foundation; either version 2 of the License, or
#  (at your option) any later version.
#
#  This program is distributed in the hope that it will be useful,
#  but WITHOUT ANY WARRANTY; without even the implied warranty of
#  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#  GNU General Public License for more details.
#
#  You should have received a copy of the GNU General Public License
#  along with this program; if not, write to the Free Software
#  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
#
#
# Author:
# Sebastian Garcia sgarcia@exa.unicen.edu.ar, eldraco@gmail.com
#
# Changelog
# 0.8  Thu Nov  7 09:47:52 UTC 2013
#       Read the format of the biargus complete weblogs
# 0.7
#       Add the option to store the plot in a file, also to store all the resuls in a file.
# 0.6
#       Added the new time-weighted measure
#       t-TP, t-FN, t-TN, t-FP, t-Precision, t-Recall, TMeasure
#       And a lot of more stuff...
# 0.5
#       I added the fmeasure 0.5
#       Now the plot is correctly done
#       
# 0.4 
#     29 Oct 2012
#    We added counters for the background labels too. 
#        B1 is when the predicted label was negative, and the real label was background.
#        B2 is when the predicted label was positive, and the real label was background.
#        B3 is when the predicted label was background, and the real label was negative.
#        B4 is when the predicted label was background, and the real label was positive.
#        B5 is when the predicted label was background, and the real label was background.
# 0.3 
#     Oct 9 2012
#       Changed ...
# 0.2 
#     Ago 2 2012
#       Added support for plotting the fmeasures.
#     Ago 1 2012
#       Added Fmeasure2 in the output
#     Jul 30 2012
#     Added support for time based comparison of flows.
# 0.1 dic 8 2011
#       First version

# Description


# standard imports
from operator import itemgetter, attrgetter
import os
#import pwd
import string
import sys
import getopt
from datetime import datetime
from time import mktime
import copy
import subprocess


####################
# Global Variables

debug = 0
vernum = "0.9"
verbose = False

botnet_labels_amount = 0
background_labels_amount = 0

doplot = False
time_window_id = 0
time_windows_group = []
alpha = 0.01
first_sum = 0
second_sum = 1
comparison_type = ''
csv_file = ''
out_file = ''
plot_file = ''
#########


# Print version information and exit
def version():
    print "+----------------------------------------------------------------------+"
    print "| statisticsGenerator.py Version "+ vernum +"                                   |"
    print "| This program is free software; you can redistribute it and/or modify |"
    print "| it under the terms of the GNU General Public License as published by |"
    print "| the Free Software Foundation; either version 2 of the License, or    |"
    print "| (at your option) any later version.                                  |"
    print "|                                                                      |"
    print "| Author: Garcia Sebastian, sebastiangarcia@conicet.gov.ar             |"
    print "| Author: Martin Grill, grillmartin@gmail.com                          |"
    print "| Author: Jan Stiborek, honza.stiborek@gmail.com                       |"
    print "| UNICEN-ISISTAN, Argentina. CTU, Prague-ATG                           |"
    print "+----------------------------------------------------------------------+"
    print


# Print help information and exit:
def usage():
    print "+----------------------------------------------------------------------+"
    print "| statisticsGenerator.py Version "+ vernum +"                                   |"
    print "| This program is free software; you can redistribute it and/or modify |"
    print "| it under the terms of the GNU General Public License as published by |"
    print "| the Free Software Foundation; either version 2 of the License, or    |"
    print "| (at your option) any later version.                                  |"
    print "|                                                                      |"
    print "| Author: Garcia Sebastian, eldraco@gmail.com                          |"
    print "| Author: Martin Grill, grillmartin@gmail.com                          |"
    print "| Author: Jan Stiborek, honza.stiborek@gmail.com                       |"
    print "| UNICEN-ISISTAN, Argentina. CTU, Prague-ATG                           |"
    print "+----------------------------------------------------------------------+"
    print "\nusage: %s <options>" % sys.argv[0]
    print "options:"
    print "  -h, --help           Show this help message and exit"
    print "  -V, --version        Output version information and exit"
    print "  -v, --verbose        Output more information."
    print "  -D, --debug          Debug. In debug mode the statistics run live."
    print "  -f, --file           SORTED input netflow labeled file to analyze (Netflow or Argus)."
    print "  -t, --type           Type of comparison. Flow based (-t flow), time based (-t time), or weighted (-t weight)."
    print "  -T, --time           While using time based comparison, specify the time window to use in secodns. E.g. -T 120"
    print "  -p, --plot           Plot the fmeasures of all methods."
    print "  -a, --alpha          In weight mode, use this alpha for computing the score (defaults to 0.4)."
    print "  -c, --cvs            Print the final scores in cvs format into the specified file. E.g. -c results.csv"
    print "  -o, --out            Store in a log file everything that is shown in the screen. -o all-info.txt"
    print "  -P, --plot-to-file   Instead of showing the plot on the screen, store it in a file. Type of plot given by the file extension. E.g. -P all-info.eps"
    print
    sys.exit(1)


class time_windows():
    """ This class holds all the information of the current time window. The ips, methods, etc. """
    def __init__(self):
        # ID. Starts with zero so we can 
        self.id = 0
        # This will hold each IP address label for this time window
        self.ip_original_labels = {}
        # This will link us to the algorithms
        self.algorithms_dict = {}
        self.TP = 0
        self.TN = 0
        self.FN = 0
        self.FP = 0
        self.B1 = 0
        self.B2 = 0
        self.B3 = 0
        self.B4 = 0
        self.B5 = 0
        self.amount_of_unique_ips = {}
        self.amount_of_labels = {}
        # Self assign a new time window id.
        self.assign_id()
        self.lines_read = 0

    def __repr__(self):
        """ Default printing method """ 
        text= '####################################\nTime Window Number: {0}\nAmount of algorithms being used: {1}\nAmount of unique ips: {2}\nAmount of labels: {3}\nLines read: {4}\n####################################'.format(self.id, len(self.algorithms_dict), self.amount_of_unique_ips, self.amount_of_labels, self.lines_read) 
        return text

    def assign_id(self):
        """ Assign an id to this time window. It is the time window number. """
        global time_window_id
        global debug
        time_window_id = time_window_id + 1
        self.id = time_window_id
        #if debug:
        #    print ' > Time window id:{0}'.format(self.id)

    def clean_ip_labels(self):
        """ Clean the ip labels dict for each algorithm """
        self.ip_original_labels = {}

        for alg in self.algorithms_dict:
            self.algorithms_dict[alg].ip_labels = {}
            self.algorithms_dict[alg].ip_current_labels = {}
            self.algorithms_dict[alg].clean_current_errors()

    def algorithms_labels_for_this_ip(self, ip):
        """ Get an ip and return the list of labels for each algorithm """
        resp = {}
        for alg in self.algorithms_dict:
            try:
                resp[alg] = self.algorithms_dict[alg].ip_labels[ip]
            except KeyError:
                resp[alg] = ''

        return resp

    def add_ip_label(self, ip, label):
        """ Get an ip and the real label. Check if the ip is new in this time window. Store the label. If it is new, initializate the label for each algorithm"""
        global debug
        try:
            if self.ip_original_labels.has_key(ip):
                # We have already seen this ip
                #if debug:
                    #print ' > We have already seen this ip: {0}'.format(ip)

                # Did the real label changed? Verify if it needs to be changed or not according to our strategy.
                if self.ip_original_labels[ip] != label:
                    if 'background' in self.ip_original_labels[ip].lower() and 'botnet' in label.lower():
                        if debug:
                            print '\nThe label for this IP has changed in the same time window from {0} to {1}!'.format(self.ip_original_labels[ip], label)
                        # Decrease the amount of ips for the previous label
                        self.amount_of_unique_ips[self.ip_original_labels[ip]] -= 1
                        # Increase the amount of ips for the new label
                        try:
                            self.amount_of_unique_ips[label] += 1
                        except KeyError:
                            self.amount_of_unique_ips[label] = 1
                        # Assign the new label to the ip
                        self.ip_original_labels[ip] = label

                    elif 'normal' in self.ip_original_labels[ip].lower() and 'botnet' in label.lower(): 
                        if debug:
                            print '\nThe label for this IP has changed in the same time window from {0} to {1}!!'.format(self.ip_original_labels[ip], label)
                        # Decrease the amount of ips for the previous label
                        self.amount_of_unique_ips[self.ip_original_labels[ip]] -= 1
                        # Increase the amount of ips for the new label
                        try:
                            self.amount_of_unique_ips[label] += 1
                        except KeyError:
                            self.amount_of_unique_ips[label] = 1
                        # Assign the new label to the ip
                        self.ip_original_labels[ip] = label
                    elif 'background' in self.ip_original_labels[ip].lower() and 'normal' in label.lower() and 'from' in label.lower(): 
                        if debug:
                            print '\nThe label for this IP has changed in the same time window from {0} to {1}!!!'.format(self.ip_original_labels[ip], label)
                        # Decrease the amount of ips for the previous label
                        self.amount_of_unique_ips[self.ip_original_labels[ip]] -= 1
                        # Increase the amount of ips for the new label
                        try:
                            self.amount_of_unique_ips[label] += 1
                        except KeyError:
                            self.amount_of_unique_ips[label] = 1
                        # Assign the new label to the ip
                        self.ip_original_labels[ip] = label
                    elif 'botnet' in self.ip_original_labels[ip].lower() and 'cc' not in self.ip_original_labels[ip].lower() and 'cc' in label.lower(): 
                        if debug:
                            print '\nThe label for this IP has changed in the same time window from {0} to {1}!!!!'.format(self.ip_original_labels[ip], label)
                        # Decrease the amount of ips for the previous label
                        self.amount_of_unique_ips[self.ip_original_labels[ip]] -= 1
                        # Increase the amount of ips for the new label
                        try:
                            self.amount_of_unique_ips[label] += 1
                        except KeyError:
                            self.amount_of_unique_ips[label] = 1
                        # Assign the new label to the ip
                        self.ip_original_labels[ip] = label


                # Did the label of the algorithms change?
                for alg in self.algorithms_dict:
                    if self.algorithms_dict[alg].ip_labels[ip] != self.algorithms_dict[alg].ip_current_labels[ip]:
                        # Yes. The algorithm changed the label.

                        # If the previous predicted label does not include the positive label for this alg and the new predicted label includes the positive label for this alg, then the new predicted should be the taken into account.

                        #if self.algorithms_dict[alg].ip_labels[ip] != self.algorithms_dict[alg].algorithm_labels[1] and self.algorithms_dict[alg].ip_current_labels[ip] == self.algorithms_dict[alg].algorithm_labels[1]:
                        if self.algorithms_dict[alg].algorithm_labels[1] not in self.algorithms_dict[alg].ip_labels[ip] and self.algorithms_dict[alg].algorithm_labels[1] in self.algorithms_dict[alg].ip_current_labels[ip]:
                            # Yes. We should change the previous predicted label to the new predicted label
                            if debug:
                                print ' > In alg {0}, for ip {1} the label changed from {2} to {3}.'.format(self.algorithms_dict[alg].name, ip, self.algorithms_dict[alg].ip_labels[ip], self.algorithms_dict[alg].ip_current_labels[ip])

                            self.algorithms_dict[alg].ip_labels[ip] = self.algorithms_dict[alg].ip_current_labels[ip]

            else:
                # We did not see this ip yet. It is new

                # Is the new label a valid one?
                # Note that every algorithm has the real_labels dict on them. We took the labels for AllPositive
                #if debug:
                    #print ' > First time we see this ip: {0}'.format(ip)

                #if label in self.algorithms_dict['AllPositive'].real_labels.values():
                # It is valid

                # Assign it to the ip
                self.ip_original_labels[ip] = label

                # Add 1 to the amount of different ips seen

                # Store the amount of unique ips for each label
                try:
                    self.amount_of_unique_ips[label] += 1
                except KeyError:
                    self.amount_of_unique_ips[label] = 1

                # Assign the predicted label of each algorithm as the final label for this ip for the algorithm. As this is the first time we see this ip, there is no conflict.
                for alg in self.algorithms_dict:
                    self.algorithms_dict[alg].ip_labels[ip] = self.algorithms_dict[alg].ip_current_labels[ip]

                #if debug:
                    #print ' > New ip found: {0}. Real label: {1}.'.format(ip, label)

        except Exception as inst:
            if debug:
                print 'Some problem in add_ip_label() method of class time_window'
            print type(inst)     # the exception instance
            print inst.args      # arguments stored in .args
            print inst           # __str__ allows args to printed directly
            x, y = inst          # __getitem__ allows args to be unpacked directly
            print 'x =', x
            print 'y =', y
            exit(-1)


    def compute_weighted_errors(self):
        """ For each algorithm in this time window compute weigthed errors """
        global debug
        global alpha
        global first_sum
        global second_sum

        try:

            try:
                import scipy
            except ImportError:
                print "WARNING! You don't have python-scipy installed. apt-get install python-scipy"
                exit (-1)

            if debug:
                print '\n > Compute weighted errors'

            correcting_function = scipy.exp( -alpha * ( self.id + first_sum ) ) + second_sum

            if debug:
                print ' > Correcting function for time window {0}: {1}'.format(self.id, correcting_function)
                #for alg in self.algorithms_dict:
                    #print alg
                    #print '\t Ip labels: {0}'.format(self.algorithms_dict[alg].ip_labels)
                    #print '\t Ip Original labels: {0}'.format(self.algorithms_dict[alg].algorithm_labels)
                    #print '\t Ip Real labels: {0}'.format(self.algorithms_dict[alg].real_labels)
                    #print '\t', self.algorithms_dict[alg].current_reportprint(30)

            # Compute and Store the weighted values
            for alg in self.algorithms_dict:
                self.algorithms_dict[alg].compute_weighted_metrics(correcting_function, self.amount_of_unique_ips)


        except Exception as inst:
            if debug:
                print 'Some problem in compute_weighted_errors() method of class time_window'
            print type(inst)     # the exception instance
            print inst.args      # arguments stored in .args
            print inst           # __str__ allows args to printed directly
            x, y = inst          # __getitem__ allows args to be unpacked directly
            print 'x =', x
            print 'y =', y
            exit(-1)



    def compute_errors(self):
        """ Get the real label and the label of each algorithm and compute the errors"""
        global debug

        try:
            if debug or verbose:
                print '\nRunning metrics...'
            for alg in self.algorithms_dict:
                # for each algorithm

                # For each ip
                for ip in self.ip_original_labels:
                    # The real label
                    reallabel = self.ip_original_labels[ip]

                    # The algorithms predicted label
                    predictedlabel = self.algorithms_dict[alg].ip_labels[ip]

                    if debug:
                        print ' > Computing errors for algorithm: {0}. Ip: {1}. Real label: {2}. Predicted label: {3}'.format( alg, ip, reallabel, predictedlabel)

                    # Is the predicted label the negative label?
                    #if self.algorithms_dict[alg].algorithm_labels[0] == predictedlabel :
                    if self.algorithms_dict[alg].algorithm_labels[0] in predictedlabel :
                        # This algorithm said Negative 

                        #if reallabel == self.algorithms_dict[alg].real_labels[0]:
                        if self.algorithms_dict[alg].real_labels[0] in reallabel:
                            # Real is Normal. True Negative.
                            self.algorithms_dict[alg].addTN()
                            if debug or verbose:
                                print '\tReal Label: \x1b\x5b1;33;40m{0}\x1b\x5b0;0;40m, {1}: {2}. Decision \x1b\x5b1;33;40mTN\x1b\x5b0;0;40m'.format(reallabel, self.algorithms_dict[alg].name, predictedlabel)

                        #elif reallabel == self.algorithms_dict[alg].real_labels[1]:
                        elif self.algorithms_dict[alg].real_labels[1] in reallabel:
                            # Real is Botnet. False Negative.
                            self.algorithms_dict[alg].addFN()
                            if debug or verbose:
                                print '\tReal Label: \x1b\x5b1;31;40m{0}\x1b\x5b0;0;40m, {1}: {2}. Decision: \x1b\x5b1;31;40mFN\x1b\x5b0;0;40m'.format(reallabel, self.algorithms_dict[alg].name, predictedlabel)

                        #elif reallabel == self.algorithms_dict[alg].real_labels[2]:
                        elif self.algorithms_dict[alg].real_labels[2] in reallabel:
                            # Real is Background. 
                            self.algorithms_dict[alg].addB1()

                    # Is the predicted label the positive label?
                    # This comparison is to catch 'Botnet6' predicted label correctly as 'Botnet' real label.
                    # Should not catch CAMNEP labels
                    elif self.algorithms_dict[alg].algorithm_labels[1] in predictedlabel:
                        # This algorithm said Positive 

                        #if reallabel == self.algorithms_dict[alg].real_labels[0]:
                        if self.algorithms_dict[alg].real_labels[0] in reallabel:
                            # Real is Normal. False Positive
                            self.algorithms_dict[alg].addFP()
                            if debug or verbose:
                                print '\tReal Label: \x1b\x5b1;31;40m{0}\x1b\x5b0;0;40m, {1}: {2}. Decision: \x1b\x5b1;31;40mFP\x1b\x5b0;0;40m'.format(reallabel, self.algorithms_dict[alg].name, predictedlabel)

                        #elif reallabel == self.algorithms_dict[alg].real_labels[1]:
                        elif self.algorithms_dict[alg].real_labels[1] in reallabel:
                            # Real is Botnet. True Positive.
                            self.algorithms_dict[alg].addTP()
                            if debug or verbose:
                                print '\tReal Label: \x1b\x5b1;33;40m{0}\x1b\x5b0;0;40m, {1}: {2}. Decision \x1b\x5b1;33;40mTP\x1b\x5b0;0;40m'.format(reallabel, self.algorithms_dict[alg].name, predictedlabel)

                        #elif reallabel == self.algorithms_dict[alg].real_labels[2]:
                        elif self.algorithms_dict[alg].real_labels[2] in reallabel:
                            # Real is Background.
                            self.algorithms_dict[alg].addB2()

                    # Is it the background label?
                    #elif self.algorithms_dict[alg].algorithm_labels[2] == predictedlabel :
                    elif self.algorithms_dict[alg].algorithm_labels[2] in predictedlabel :
                        # This algorithm said Background 

                        #if reallabel == self.algorithms_dict[alg].real_labels[0]:
                        if self.algorithms_dict[alg].real_labels[0] in reallabel:
                            # Real is Normal. 
                            self.algorithms_dict[alg].addB3()

                        #elif reallabel == self.algorithms_dict[alg].real_labels[1]:
                        elif self.algorithms_dict[alg].real_labels[1] in reallabel:
                            # Real is Botnet.
                            #self.algorithms_dict[alg].addB4()

                            # Not sure if counting a FN here is ok.
                            # Real is Botnet. False Negative.
                            self.algorithms_dict[alg].addFN()
                            if debug or verbose:
                                print '\tReal Label: \x1b\x5b1;31;40m{0}\x1b\x5b0;0;40m, {1}: {2}. Decision: \x1b\x5b1;31;40mFN\x1b\x5b0;0;40m'.format(reallabel, self.algorithms_dict[alg].name, predictedlabel)

                        #elif reallabel == self.algorithms_dict[alg].real_labels[2]:
                        elif self.algorithms_dict[alg].real_labels[2] in reallabel:
                            # Real is Background.
                            self.algorithms_dict[alg].addB5()

        except Exception as inst:
            if debug:
                print 'Some problem in compute_error() method of class time_window'
            print type(inst)     # the exception instance
            print inst.args      # arguments stored in .args
            print inst           # __str__ allows args to printed directly
            x, y = inst          # __getitem__ allows args to be unpacked directly
            print 'x =', x
            print 'y =', y
            exit(-1)







class algorithm():
    """ This class is for storing and generating the metrics of each algorithm """
    def __init__(self):
        # These are the cumulative values. Useful for the time-based comparison without weight.
        self.name = ""
        self.TP = 0 # a
        self.TN = 0 # d
        self.FP = 0 # c
        self.FN = 0 # b
        self.B1 = 0 # Predicted negative and real was background
        self.B2 = 0 # Predicted positive and real was background
        self.B3 = 0 # Predicted background and real was negative
        self.B4 = 0 # Predicted background and real was positive
        self.B5 = 0 # Predicted background and real was background
        self.TPR = -1
        self.TNR = -1
        self.FNR = -1
        self.FPR = -1
        self.Accuracy = -1
        self.Precision = -1
        self.ErrorRate = -1
        self.fmeasure1 = -1
        self.fmeasure2 = -1
        self.fmeasure05 = -1

        # These are the values for the current time window only!
        self.cTP = 0 # a
        self.cTN = 0 # d
        self.cFP = 0 # c
        self.cFN = 0 # b
        self.cB1 = 0 # Predicted negative and real was background
        self.cB2 = 0 # Predicted positive and real was background
        self.cB3 = 0 # Predicted background and real was negative
        self.cB4 = 0 # Predicted background and real was positive
        self.cB5 = 0 # Predicted background and real was background
        self.cTPR = -1
        self.cTNR = -1
        self.cFNR = -1
        self.cFPR = -1
        self.cAccuracy = -1
        self.cPrecision = -1
        self.cErrorRate = -1
        self.cfmeasure1 = -1
        self.cfmeasure2 = -1
        self.cfmeasure05 = -1

        # These are the cumulative weighted values
        self.t_TP = 0 # a
        self.t_TN = 0 # d
        self.t_FP = 0 # c
        self.t_FN = 0 # b
        self.t_B1 = 0 # Predicted negative and real was background
        self.t_B2 = 0 # Predicted positive and real was background
        self.t_B3 = 0 # Predicted background and real was negative
        self.t_B4 = 0 # Predicted background and real was positive
        self.t_B5 = 0 # Predicted background and real was background
        self.t_TPR = -1
        self.t_TNR = -1
        self.t_FNR = -1
        self.t_FPR = -1
        self.t_Accuracy = -1
        self.t_Precision = -1
        self.t_ErrorRate = -1
        self.t_fmeasure1 = -1
        self.t_fmeasure2 = -1
        self.t_fmeasure05 = -1

        # These are the weighted values for the current time window only!
        self.ct_TP = 0 # a
        self.ct_TN = 0 # d
        self.ct_FP = 0 # c
        self.ct_FN = 0 # b
        self.ct_B1 = 0 # Predicted negative and real was background
        self.ct_B2 = 0 # Predicted positive and real was background
        self.ct_B3 = 0 # Predicted background and real was negative
        self.ct_B4 = 0 # Predicted background and real was positive
        self.ct_B5 = 0 # Predicted background and real was background
        self.ct_TPR = -1
        self.ct_TNR = -1
        self.ct_FNR = -1
        self.ct_FPR = -1
        self.ct_Accuracy = -1
        self.ct_Precision = -1
        self.ct_ErrorRate = -1
        self.ct_fmeasure1 = -1
        self.ct_fmeasure2 = -1
        self.ct_fmeasure05 = -1

        # Which column does this alg use in the input line?
        self.headercolumn = -1
        # The algorithm's valid labels. [NegativeLabel, PositiveLabel, BackgroundLabel ]. So self.algorithm_labels[0] is the negative label, 
        # and self.algorithm_labels[1] is the positive label and self.algorithm_labels[2] is the background label. Background label is optional.
        self.algorithm_labels = {}

        # The file real labels. [0] is Normal Label, [1] is Botnet label, [2] is Background label. There is ONLY ONE label for each category. 
        # Can not be two normal labels. In the past we had both 'Normal' and 'Legitimate' as normal labels. BEWARE! Check your file!
        self.real_labels = {}

        # Vectors for plotting common errors
        self.plotTP = []
        self.plotTN = []
        self.plotFP = []
        self.plotFN = []
        self.plotTPR = []
        self.plotTNR = []
        self.plotFNR = []
        self.plotFPR = []
        self.plotAccuracy = []
        self.plotPrecision = []
        self.plotErrorRate = []
        self.plotfmeasure1 = []
        self.plotfmeasure2 = []
        self.plotfmeasure05 = []
        # Vectors for plotting weighted errors
        self.t_plotTP = []
        self.t_plotTN = []
        self.t_plotFP = []
        self.t_plotFN = []
        self.t_plotTPR = []
        self.t_plotTNR = []
        self.t_plotFNR = []
        self.t_plotFPR = []
        self.t_plotAccuracy = []
        self.t_plotPrecision = []
        self.t_plotErrorRate = []
        self.t_plotfmeasure1 = []
        self.t_plotfmeasure2 = []
        self.t_plotfmeasure05 = []

        # This will store a label for each IP address seen for this algorithm in the current time window. This is the final label for that ip.
        self.ip_labels = {}
        # This will store the current label seen for each IP address in the current time window. This label is not the final decision.
        self.ip_current_labels = {}

    def clean_current_errors(self):
        """ Clean the errors for the current time window and the weighted errors. Do not delete the cumulative values """
        try:
            # These are the values for the current time window only!
            self.cTP = 0 # a
            self.cTN = 0 # d
            self.cFP = 0 # c
            self.cFN = 0 # b
            self.cB1 = 0 # Predicted negative and real was background
            self.cB2 = 0 # Predicted positive and real was background
            self.cB3 = 0 # Predicted background and real was negative
            self.cB4 = 0 # Predicted background and real was positive
            self.cB5 = 0 # Predicted background and real was background
            self.cTPR = -1
            self.cTNR = -1
            self.cFNR = -1
            self.cFPR = -1
            self.cAccuracy = -1
            self.cPrecision = -1
            self.cErrorRate = -1
            self.cfmeasure1 = -1
            self.cfmeasure2 = -1
            self.cfmeasure05 = -1

            # These are the weighted value for the current time window only!
            self.ct_TP = 0 # a
            self.ct_TN = 0 # d
            self.ct_FP = 0 # c
            self.ct_FN = 0 # b
            self.ct_B1 = 0 # Predicted negative and real was background
            self.ct_B2 = 0 # Predicted positive and real was background
            self.ct_B3 = 0 # Predicted background and real was negative
            self.ct_B4 = 0 # Predicted background and real was positive
            self.ct_B5 = 0 # Predicted background and real was background
            self.ct_TPR = -1
            self.ct_TNR = -1
            self.ct_FNR = -1
            self.ct_FPR = -1
            self.ct_Accuracy = -1
            self.ct_Precision = -1
            self.ct_ErrorRate = -1
            self.ct_fmeasure1 = -1
            self.ct_fmeasure2 = -1
            self.ct_fmeasure05 = -1

        except Exception as inst:
            if debug:
                print 'Some problem in clean_current_errors() method of class algorithm'
            print type(inst)     # the exception instance
            print inst.args      # arguments stored in .args
            print inst           # __str__ allows args to printed directly
            x, y = inst          # __getitem__ allows args to be unpacked directly
            print 'x =', x
            print 'y =', y
            exit(-1)


    def __repr__(self):
        """ Default printing method """ 
        return repr('{0} TP={1}, TN={2}, FP={3}, FN={4} TPR={5:.2f}, TNR={6:.2f}, FPR={7:.2f}, FNR={8:.2f}, Precision={9:.2f}, Accuracy={10:.2f}, ErrorRate={11:.2f}, FM1={12:.2f}, FM2={13:.2f}, FM05={14:.2f}'.format(self.name, self.TP, self.TN, self.FP, self.FN, self.TPR, self.TNR, self.FPR, self.FNR, self.Precision, self.Accuracy, self.ErrorRate, self.fmeasure1, self.fmeasure2, self.fmeasure05))

    def compute_error(self, predictedlabel, reallabel):
        """ Get the predicted label and the real label and compute the error type. Also verifies that labels are valid for this algorithm """
        global debug
        try:
            if debug:
                print ' > Computing errors for algorithm: {0}'.format(self.name)
            # Verify that the new label is valid
            # The final 'or' is to accept labels that have a number at the end like 'Botnet6'
            if (predictedlabel in self.algorithm_labels.values() and reallabel in self.real_labels.values()) or predictedlabel[:-1] in self.algorithm_labels.values() or predictedlabel[:-2] in self.algorithm_labels.values():
                # They are valid

                # Is it the negative label?
                #if self.algorithm_labels[0] == predictedlabel :
                if self.algorithm_labels[0] in predictedlabel :
                    # This algorithm said Negative 

                    #if reallabel == self.real_labels[0]:
                    if self.real_labels[0] in reallabel:
                        # Real is Normal. True Negative.
                        self.addTN()
                        if debug or verbose:
                            print '\tReal Label: \x1b\x5b1;33;40m{0}\x1b\x5b0;0;40m, {1}: {2}. Decision \x1b\x5b1;33;40mTN\x1b\x5b0;0;40m'.format(reallabel, self.name, predictedlabel)

                    #elif reallabel == self.real_labels[1]:
                    elif self.real_labels[1] in reallabel:
                        # Real is Botnet. False Negative.
                        self.addFN()
                        if debug or verbose:
                            print '\tReal Label: \x1b\x5b1;31;40m{0}\x1b\x5b0;0;40m, {1}: {2}. Decision: \x1b\x5b1;31;40mFN\x1b\x5b0;0;40m'.format(reallabel, self.name, predictedlabel)

                    #elif reallabel == self.real_labels[2]:
                    elif self.real_labels[2] in reallabel:
                        # Real is Background.
                        self.addB1()
                        if debug:
                            print '\t\tBackground1'

                # Is it the positive label?
                # This comparison is to catch 'Botnet6' predicted label correctly as 'Botnet' real label.
                # Should not catch CAMNEP labels
                elif self.algorithm_labels[1] in predictedlabel:
                    # This algorithm said Positive 

                    #if reallabel == self.real_labels[0]:
                    if self.real_labels[0] in reallabel: 
                        # Real is Normal. False Positive
                        self.addFP()
                        if debug or verbose:
                            print '\tReal Label: \x1b\x5b1;31;40m{0}\x1b\x5b0;0;40m, {1}: {2}. Decision: \x1b\x5b1;31;40mFP\x1b\x5b0;0;40m'.format(reallabel, self.name, predictedlabel)

                    #elif reallabel == self.real_labels[1]:
                    elif self.real_labels[1] in reallabel:
                        # Real is Botnet. True Positive.
                        self.addTP()
                        if debug or verbose:
                            print '\tReal Label: \x1b\x5b1;33;40m{0}\x1b\x5b0;0;40m, {1}: {2}. Decision \x1b\x5b1;33;40mTP\x1b\x5b0;0;40m'.format(reallabel, self.name, predictedlabel)

                    #elif reallabel == self.real_labels[2]:
                    elif self.real_labels[2] in reallabel:
                        # Real is Background. 
                        self.addB2()
                        if debug:
                            print '\t\tBackground2'

                # Is it the background label?
                #elif self.algorithm_labels[2] == predictedlabel :
                elif self.algorithm_labels[2] in predictedlabel :
                    # This algorithm said Background 

                    #if reallabel == self.real_labels[0]:
                    if self.real_labels[0] in reallabel:
                        # Real is Normal.
                        self.addB3()
                        if debug:
                            print '\t\tBackground3'

                    #elif reallabel == self.real_labels[1]:
                    elif self.real_labels[1] in reallabel:
                        # Real is Botnet.
                        self.addB4()
                        if debug:
                            print '\t\tBackground4'

                    #elif reallabel == self.real_labels[2]:
                    elif self.real_labels[2] in reallabel:
                        # Real is Background. 
                        self.addB5()
                        if debug:
                            print '\t\tBackground5'

            else:
                # They are not valid
                print 'WARNING! An invalid label was given for algorithm {0}: Algorithm accepted labels:{1}, algorithm predicted label:{2}. Real accepted labels:{3}, given real label: {4}'.format(self.name, self.algorithm_labels, predictedlabel, self.real_labels, reallabel)
                exit(-1)
        except Exception as inst:
            if debug:
                print 'Some problem in compute_error() method of class algorithm'
            print type(inst)     # the exception instance
            print inst.args      # arguments stored in .args
            print inst           # __str__ allows args to printed directly
            x, y = inst          # __getitem__ allows args to be unpacked directly
            print 'x =', x
            print 'y =', y
            exit(-1)


    def reportprint(self, longest_name):
        """ The reported values """ 
        # I still did not found out how to use longest_name to change the width of the columns...
        text = '{0:30} TP={1:8}, TN={2:8}, FP={3:8}, FN={4:8}, TPR={5:.3f}, TNR={6:.3f}, FPR={7:.3f}, FNR={8:.3f}, Precision={9:7.4f}, Accuracy={10:5.4f}, ErrorRate={11:5.3f}, FM1={12:7.4f}, FM2={13:7.4f}, FM05={14:7.4f}, B1={15:8}, B2={16:8}, B3={17:3}, B4={18:3}, B5={19:3}'.format(self.name, self.TP, self.TN, self.FP, self.FN, self.TPR, self.TNR, self.FPR, self.FNR, self.Precision, self.Accuracy, self.ErrorRate, self.fmeasure1, self.fmeasure2, self.fmeasure05, self.B1, self.B2, self.B3, self.B4, self.B5)
        print text

    def report_CSV_print(self, longest_name, csv_handler):
        """ The reported values in csv format """ 
        # I still did not found out how to use longest_name to change the width of the columns...
        text = '{0:30},{1:8},{2:8},{3:8},{4:8},{5:.3f},{6:.3f},{7:.3f},{8:.3f},{9:7.4f},{10:5.4f},{11:5.3f},{12:7.4f},{13:7.4f},{14:7.4f},{15:8},{16:8},{17:3},{18:3},{19:3}'.format(self.name, self.TP, self.TN, self.FP, self.FN, self.TPR, self.TNR, self.FPR, self.FNR, self.Precision, self.Accuracy, self.ErrorRate, self.fmeasure1, self.fmeasure2, self.fmeasure05, self.B1, self.B2, self.B3, self.B4, self.B5)
        csv_handler.write(text+'\n')

    def current_reportprint(self, longest_name):
        """ The reported values """ 
        # I still did not found out how to use longest_name to change the width of the columns...
        print '{0:30} TP={1:8}, TN={2:8}, FP={3:8}, FN={4:8}, TPR={5:.3f}, TNR={6:.3f}, FPR={7:.3f}, FNR={8:.3f}, Precision={9:7.4f}, Accuracy={10:5.4f}, ErrorRate={11:5.3f}, FM1={12:7.4f}, FM2={13:7.4f}, FM05={14:7.4f}, B1={15:8}, B2={16:8}, B3={17:3}, B4={18:3}, B5={19:3}'.format(self.name, self.cTP, self.cTN, self.cFP, self.cFN, self.cTPR, self.cTNR, self.cFPR, self.cFNR, self.cPrecision, self.cAccuracy, self.cErrorRate, self.cfmeasure1, self.cfmeasure2, self.cfmeasure05, self.cB1, self.cB2, self.cB3, self.cB4, self.cB5)

    def weighted_reportprint(self, longest_name):
        """ The reported values """ 
        # I still did not found out how to use longest_name to change the width of the columns...
        text = '{0:30} t-TP={1:.4f}, t-TN={2:8}, t-FP={3:8}, t-FN={4:.4f}, t-TPR={5:.3f}, t-TNR={6:.3f}, t-FPR={7:.3f}, t-FNR={8:.3f}, t-Precision={9:7.4f}, t-Accuracy={10:5.4f}, t-ErrorRate={11:5.3f}, t-FM1={12:7.4f}, t-FM2={13:7.4f}, t-FM05={14:7.4f}, t-B1={15:8}, t-B2={16:8}, t-B3={17:3}, t-B4={18:3}, t-B5={19:3}'.format(self.name, self.t_TP, self.t_TN, self.t_FP, self.t_FN, self.t_TPR, self.t_TNR, self.t_FPR, self.t_FNR, self.t_Precision, self.t_Accuracy, self.t_ErrorRate, self.t_fmeasure1, self.t_fmeasure2, self.t_fmeasure05, self.t_B1, self.t_B2, self.t_B3, self.t_B4, self.t_B5)
        print text

    def weighted_report_CSV_print(self, longest_name, csv_handler):
        """ The reported values """ 
        # If there is a csv file, write on it
        # I still did not found out how to use longest_name to change the width of the columns...
        text = '{0:30},{1:.4f},{2:8},{3:8},{4:.4f},{5:.3f},{6:.3f},{7:.3f},{8:.3f},{9:7.4f},{10:5.4f},{11:5.3f},{12:7.4f},{13:7.4f},{14:7.4f},{15:8},{16:8},{17:3},{18:3},{19:3}'.format(self.name, self.t_TP, self.t_TN, self.t_FP, self.t_FN, self.t_TPR, self.t_TNR, self.t_FPR, self.t_FNR, self.t_Precision, self.t_Accuracy, self.t_ErrorRate, self.t_fmeasure1, self.t_fmeasure2, self.t_fmeasure05, self.t_B1, self.t_B2, self.t_B3, self.t_B4, self.t_B5)
        csv_handler.write(text+'\n')

    def weighted_current_reportprint(self, longest_name):
        """ The reported values """ 
        # I still did not found out how to use longest_name to change the width of the columns...
        print '{0:30} t-TP={1:.4f}, t-TN={2:8}, t-FP={3:8}, t-FN={4:.4f}, t-TPR={5:.3f}, t-TNR={6:.3f}, t-FPR={7:.3f}, t-FNR={8:.3f}, t-Precision={9:7.4f}, t-Accuracy={10:5.4f}, t-ErrorRate={11:5.3f}, t-FM1={12:7.4f}, t-FM2={13:7.4f}, t-FM05={14:7.4f}, t-B1={15:8}, t-B2={16:8}, t-B3={17:3}, t-B4={18:3}, t-B5={19:3}'.format(self.name, self.ct_TP, self.ct_TN, self.ct_FP, self.ct_FN, self.ct_TPR, self.ct_TNR, self.ct_FPR, self.ct_FNR, self.ct_Precision, self.ct_Accuracy, self.ct_ErrorRate, self.ct_fmeasure1, self.ct_fmeasure2, self.ct_fmeasure05, self.ct_B1, self.ct_B2, self.ct_B3, self.ct_B4, self.ct_B5)

    def addB1(self):
        """ Predicted negative but real was background """ 
        self.B1 = self.B1 + 1
        self.cB1 = self.cB1 + 1

    def addB2(self):
        """ Predicted positive but real was background """ 
        self.B2 = self.B2 + 1
        self.cB2 = self.cB2 + 1

    def addB3(self):
        """ Predicted background and real was negative """ 
        self.B3 = self.B3 + 1
        self.cB3 = self.cB3 + 1

    def addB4(self):
        """ Predicted background and real was positive """ 
        self.B4 = self.B4 + 1
        self.cB4 = self.cB4 + 1

    def addB5(self):
        """ Predicted background and real was background """ 
        self.B5 = self.B5 + 1
        self.cB5 = self.cB5 + 1

    def addTP(self):
        """ Add a True positive to this algorithm """ 
        self.TP = self.TP + 1
        self.cTP = self.cTP + 1
        self.computeMetrics()

    def addTN(self):
        """ Add a True negative to this algorithm """ 
        self.TN = self.TN + 1
        self.cTN = self.cTN + 1
        self.computeMetrics()

    def addFP(self):
        """ Add a False positive to this algorithm """ 
        self.FP = self.FP + 1
        self.cFP = self.cFP + 1
        self.computeMetrics()

    def addFN(self):
        """ Add a False negative to this algorithm """ 
        self.FN = self.FN + 1
        self.cFN = self.cFN + 1
        self.computeMetrics()

    def updateplot(self):
        """ Update the plot with the new values """ 
        self.plotTP.append(self.TP)
        self.plotTN.append(self.TN)
        self.plotFP.append(self.FP)
        self.plotFN.append(self.FN)
        self.plotTPR.append(self.TPR)
        self.plotTNR.append(self.TNR)
        self.plotFPR.append(self.FPR)
        self.plotFNR.append(self.FNR)
        self.plotPrecision.append(self.Precision)
        self.plotAccuracy.append(self.Accuracy)
        self.plotErrorRate.append(self.ErrorRate)
        self.plotfmeasure1.append(self.fmeasure1)
        self.plotfmeasure2.append(self.fmeasure2)
        self.plotfmeasure05.append(self.fmeasure05)

    def update_weighted_plot(self):
        """ Update the plot with the new values """ 
        self.t_plotTP.append(self.t_TP)
        self.t_plotTN.append(self.t_TN)
        self.t_plotFP.append(self.t_FP)
        self.t_plotFN.append(self.t_FN)
        self.t_plotTPR.append(self.t_TPR)
        self.t_plotTNR.append(self.t_TNR)
        self.t_plotFPR.append(self.t_FPR)
        self.t_plotFNR.append(self.t_FNR)
        self.t_plotPrecision.append(self.t_Precision)
        self.t_plotAccuracy.append(self.t_Accuracy)
        self.t_plotErrorRate.append(self.t_ErrorRate)
        self.t_plotfmeasure1.append(self.t_fmeasure1)
        self.t_plotfmeasure2.append(self.t_fmeasure2)
        self.t_plotfmeasure05.append(self.t_fmeasure05)

    def compute_weighted_metrics(self, correcting_function, amount_of_unique_ips):
        """ Compute the weighted metrics. Receives the correcting_function value and the amount of labels in the current time window """ 
        # t-tp score
        try:
            # Current value
            for rl in amount_of_unique_ips:
                # 1 is for the positive class or botnet class here
                if self.real_labels[1] in rl:
                    temp = amount_of_unique_ips[rl]
                    break
                else:
                    temp = 0

            #self.ct_TP = ( self.cTP * float(correcting_function) ) / amount_of_unique_ips[self.real_labels[1]]
            self.ct_TP = ( self.cTP * float(correcting_function) ) / temp
            # Cumulative value
            self.t_TP = self.t_TP + self.ct_TP
        except ZeroDivisionError:
            # ValueError was for dividing by 0. KeyError was if we still have no amount of ips with that label
            pass
        except KeyError, ValueError:
            if debug:
                print 'WARNING, something is broken on compute_weighted_metrics'

        # t-fn score
        try:
            for rl in amount_of_unique_ips:
                # 1 is for the positive class or botnet class here
                if self.real_labels[1] in rl:
                    temp = amount_of_unique_ips[rl]
                    break
                else:
                    temp = 0
            #self.ct_FN = ( self.cFN * float(correcting_function) ) / amount_of_unique_ips[self.real_labels[1]]
            self.ct_FN = ( self.cFN * float(correcting_function) ) / temp
            self.t_FN = self.t_FN + self.ct_FN
        except ZeroDivisionError:
            # ValueError was for dividing by 0. KeyError was if we still have no amount of ips with that label
            pass
        except KeyError, ValueError:
            if debug:
                print 'WARNING, something is broken on compute_weighted_metrics'

        # t-fp score. 0 is normal ips
        try:
            for rl in amount_of_unique_ips:
                if self.real_labels[0] in rl:
                    temp = float(amount_of_unique_ips[rl])
                    break
                else:
                    temp = 0
            #self.ct_FP = self.cFP / float(amount_of_unique_ips[self.real_labels[0]])
            self.ct_FP = self.cFP / temp
            self.t_FP = self.t_FP + self.ct_FP
        except ZeroDivisionError:
            # ValueError was for dividing by 0. KeyError was if we still have no amount of ips with that label
            pass
        except KeyError, ValueError:
            if debug:
                print 'WARNING, something is broken on compute_weighted_metrics'

        # t-tn score. 0 is normal ips
        try:
            for rl in amount_of_unique_ips:
                if self.real_labels[0] in rl:
                    temp = float(amount_of_unique_ips[rl])
                    break
                else:
                    temp = 0
            #self.ct_TN = self.cTN / float(amount_of_unique_ips[self.real_labels[0]])
            self.ct_TN = self.cTN / temp
            self.t_TN = self.t_TN + self.ct_TN
        except ZeroDivisionError:
            # ValueError was for dividing by 0. KeyError was if we still have no amount of ips with that label
            pass
        except KeyError, ValueError:
            if debug:
                print 'WARNING, something is broken on compute_weighted_metrics'


        # t-b1 score. 2 is background ips
        try:
            for rl in amount_of_unique_ips:
                if self.real_labels[2] in rl:
                    temp = float(amount_of_unique_ips[rl])
                    break
                else:
                    temp = 0
            #self.ct_B1 = self.cB1 / float(amount_of_unique_ips[self.real_labels[2]])
            self.ct_B1 = self.cB1 / temp
            self.t_B1 = self.t_B1 + self.ct_B1
        except ZeroDivisionError:
            # ValueError was for dividing by 0. KeyError was if we still have no amount of ips with that label
            pass
        except KeyError, ValueError:
            if debug:
                print 'WARNING, something is broken on compute_weighted_metrics'

        # t-b2 score. 2 is background ips
        try:
            for rl in amount_of_unique_ips:
                if self.real_labels[2] in rl:
                    temp = float(amount_of_unique_ips[rl])
                    break
                else:
                    temp = 0
            #self.ct_B2 = self.cB2 / float(amount_of_unique_ips[self.real_labels[2]])
            self.ct_B2 = self.cB2 / temp
            self.t_B2 = self.t_B2 + self.ct_B2
        except ZeroDivisionError:
            # ValueError was for dividing by 0. KeyError was if we still have no amount of ips with that label
            pass
        except KeyError, ValueError:
            if debug:
                print 'WARNING, something is broken on compute_weighted_metrics'

        # t-b3 score. 2 is background ips
        try:
            for rl in amount_of_unique_ips:
                if self.real_labels[2] in rl:
                    temp = float(amount_of_unique_ips[rl])
                    break
                else:
                    temp = 0
            #self.ct_B3 = self.cB3 / float(amount_of_unique_ips[self.real_labels[2]])
            self.ct_B3 = self.cB3 / temp
            self.t_B3 = self.t_B3 + self.ct_B3
        except ZeroDivisionError:
            # ValueError was for dividing by 0. KeyError was if we still have no amount of ips with that label
            pass
        except KeyError, ValueError:
            if debug:
                print 'WARNING, something is broken on compute_weighted_metrics'

        # t-b4 score. 2 is background ips
        try:
            for rl in amount_of_unique_ips:
                if self.real_labels[2] in rl:
                    temp = float(amount_of_unique_ips[rl])
                    break
                else:
                    temp = 0
            #self.ct_B4 = self.cB4 / float(amount_of_unique_ips[self.real_labels[2]])
            self.ct_B4 = self.cB4 / temp
            self.t_B4 = self.t_B4 + self.ct_B4
        except ZeroDivisionError:
            # ValueError was for dividing by 0. KeyError was if we still have no amount of ips with that label
            pass
        except KeyError, ValueError:
            if debug:
                print 'WARNING, something is broken on compute_weighted_metrics'

        # t-b5 score. 2 is background ips
        try:
            for rl in amount_of_unique_ips:
                if self.real_labels[2] in rl:
                    temp = float(amount_of_unique_ips[rl])
                    break
                else:
                    temp = 0
            #self.ct_B5 = self.cB5 / float(amount_of_unique_ips[self.real_labels[2]])
            self.ct_B5 = self.cB5 / temp
            self.t_B5 = self.t_B5 + self.ct_B5
        except ZeroDivisionError:
            # ValueError was for dividing by 0. KeyError was if we still have no amount of ips with that label
            pass
        except KeyError, ValueError:
            if debug:
                print 'WARNING, something is broken on compute_weighted_metrics'

        # t_TPR. Also Hit rate, detect rate, Recall or sensitivity. Portion of positives examples the model predicts correctly.
        try:
            self.t_TPR = ( self.t_TP ) / float(self.t_TP + self.t_FN)
        except ZeroDivisionError:
            self.t_TPR = -1
        try:
            self.ct_TPR = ( self.ct_TP ) / float(self.ct_TP + self.ct_FN)
        except ZeroDivisionError:
            # We should add 0 to the current value, that is equal to do nothing.
            pass

        # t_TNR. Also Correct-reject rate or specificity. Portion of negative examples the model predicts correctly.
        try:
            self.t_TNR = ( self.t_TN ) / float( self.t_TN + self.t_FP )
        except ZeroDivisionError:
            self.t_TNR = -1
        try:
            self.ct_TNR = ( self.ct_TN ) / float( self.ct_TN + self.ct_FP )
        except ZeroDivisionError:
            # We should add 0 to the current value, that is equal to do nothing.
            pass

        # t_FPR. Also False-alarm rate. The portion of negative examples that the model wrongly predicts as positive.
        try:
            self.t_FPR = ( self.t_FP ) / float( self.t_TN + self.t_FP )
        except ZeroDivisionError:
            self.t_FPR = -1
        try:
            self.ct_FPR = ( self.ct_FP ) / float( self.ct_TN + self.ct_FP )
        except ZeroDivisionError:
            # We should add 0 to the current value, that is equal to do nothing.
            pass

        # t_FNR. Also Miss rate. Portion of positives examples that the classifier wrongly predicts as negative.
        try:
            self.t_FNR = ( self.t_FN ) / float(self.t_TP + self.t_FN)
        except ZeroDivisionError:
            self.t_FNR = -1
        try:
            self.ct_FNR = ( self.ct_FN ) / float(self.ct_TP + self.ct_FN)
        except ZeroDivisionError:
            # We should add 0 to the current value, that is equal to do nothing.
            pass

        # t_Precision. Portion of all the examples predicted as positives that were really positives.
        try:
            self.t_Precision = ( self.t_TP ) / float(self.t_TP + self.t_FP)
        except ZeroDivisionError:
            self.t_Precision = -1
        try:
            self.ct_Precision = self.ct_TP / float(self.ct_TP + self.ct_FP)
        except ZeroDivisionError:
            # We should add 0 to the current value, that is equal to do nothing.
            pass

        # t_Accuracy. The portion of examples that the model predicts correctly
        try:
            self.t_Accuracy = ( self.t_TP + self.t_TN ) / float( self.t_TP + self.t_TN + self.t_FP + self.t_FN )
        except ZeroDivisionError:
            self.t_Accuracy = -1
        try:
            self.ct_Accuracy = ( self.ct_TP + self.ct_TN ) / float( self.ct_TP + self.ct_TN + self.ct_FP + self.ct_FN )
        except ZeroDivisionError:
            # We should add 0 to the current value, that is equal to do nothing.
            pass

        # t_Error Rate. The portion of examples that the model predicts incorrectly
        try:
            self.t_ErrorRate = ( self.t_FN + self.t_FP ) / float( self.t_TP + self.t_TN + self.t_FP + self.t_FN )
        except ZeroDivisionError:
            self.t_ErrorRate = -1
        try:
            self.ct_ErrorRate = ( self.ct_FN + self.ct_FP ) / float( self.ct_TP + self.ct_TN + self.ct_FP + self.ct_FN )
        except ZeroDivisionError:
            # We should add 0 to the current value, that is equal to do nothing.
            pass

        # T1-Measure.
        self.beta = 1.0
        # With beta=1 F-Measure is also Fscore
        try:
            self.t_fmeasure1 = ( ( (self.beta * self.beta) + 1 ) * self.t_Precision * self.t_TPR  ) / float( ( self.beta * self.beta * self.t_Precision ) + self.t_TPR )
        except ZeroDivisionError:
            self.t_fmeasure1 = -1
        try:
            self.ct_fmeasure1 = ( ( (self.beta * self.beta) + 1 ) * self.ct_Precision * self.ct_TPR  ) / float( ( self.beta * self.beta * self.ct_Precision ) + self.ct_TPR )
        except ZeroDivisionError:
            # We should add 0 to the current value, that is equal to do nothing.
            pass

        # T2-Measure.
        self.beta = 2
        # With beta=2 F-Measure gives more importance to TPR (recall)
        try:
            self.t_fmeasure2 = ( ( (self.beta * self.beta) + 1 ) * self.t_Precision * self.t_TPR  ) / float( ( self.beta * self.beta * self.t_Precision ) + self.t_TPR )
        except ZeroDivisionError:
            self.t_fmeasure2 = -1
        try:
            self.ct_fmeasure2 = ( ( (self.beta * self.beta) + 1 ) * self.ct_Precision * self.ct_TPR  ) / float( ( self.beta * self.beta * self.ct_Precision ) + self.ct_TPR )
        except ZeroDivisionError:
            # We should add 0 to the current value, that is equal to do nothing.
            pass

        # F0.5-Measure.
        self.beta = 0.5
        # With beta=2 F-Measure gives more importance to Precision 
        try:
            self.t_fmeasure05 = ( ( (self.beta * self.beta) + 1 ) * self.t_Precision * self.t_TPR  ) / float( ( self.beta * self.beta * self.t_Precision ) + self.t_TPR )
        except ZeroDivisionError:
            self.t_fmeasure05 = -1
        try:
            self.ct_fmeasure05 = ( ( (self.beta * self.beta) + 1 ) * self.ct_Precision * self.ct_TPR  ) / float( ( self.beta * self.beta * self.ct_Precision ) + self.ct_TPR )
        except ZeroDivisionError:
            # We should add 0 to the current value, that is equal to do nothing.
            pass



    def computeMetrics(self):
        """ Compute the metrics """ 
        # TPR. Also Hit rate, detect rate, Recall or sensitivity. Portion of positives examples the model predicts correctly.
        try:
            self.TPR = (self.TP) / float( self.TP + self.FN )
        except ZeroDivisionError:
            self.TPR = -1
        try:
            self.cTPR = (self.cTP) / float( self.cTP + self.cFN )
        except ZeroDivisionError:
            self.cTPR = -1

        # TNR. Also Correct-reject rate or specificity. Portion of negative examples the model predicts correctly.
        try:
            self.TNR = ( self.TN ) / float( self.TN + self.FP )
        except ZeroDivisionError:
            self.TNR = -1
        try:
            self.cTNR = ( self.cTN ) / float( self.cTN + self.cFP )
        except ZeroDivisionError:
            self.cTNR = -1

        # FPR. Also False-alarm rate. The portion of negative examples that the model wrongly predicts as positive.
        try:
            self.FPR = ( self.FP ) / float( self.TN + self.FP )
        except ZeroDivisionError:
            self.FPR = -1
        try:
            self.cFPR = ( self.cFP ) / float( self.cTN + self.cFP )
        except ZeroDivisionError:
            self.cFPR = -1

        # FNR. Also Miss rate. Portion of positives examples that the classifier wrongly predicts as negative.
        try:
            self.FNR = ( self.FN ) / float( self.TP + self.FN )
        except ZeroDivisionError:
            self.FNR = -1
        try:
            self.cFNR = ( self.cFN ) / float( self.cTP + self.cFN )
        except ZeroDivisionError:
            self.cFNR = -1

        # Precision. Portion of all the examples predicted as positives that were really positives.
        try:
            self.Precision = ( self.TP ) / float( self.TP + self.FP)
        except ZeroDivisionError:
            self.Precision = -1
        try:
            self.cPrecision = ( self.cTP ) / float( self.cTP + self.cFP)
        except ZeroDivisionError:
            self.cPrecision = -1

        # Accuracy. The portion of examples that the model predicts correctly
        try:
            self.Accuracy = ( self.TP + self.TN ) / float( self.TP + self.TN + self.FP + self.FN )
        except ZeroDivisionError:
            self.Accuracy = -1
        try:
            self.cAccuracy = ( self.cTP + self.cTN ) / float( self.cTP + self.cTN + self.cFP + self.cFN )
        except ZeroDivisionError:
            self.cAccuracy = -1

        # Error Rate. The portion of examples that the model predicts incorrectly
        try:
            self.ErrorRate = ( self.FN + self.FP ) / float( self.TP + self.TN + self.FP + self.FN )
        except ZeroDivisionError:
            self.ErrorRate = -1
        try:
            self.cErrorRate = ( self.cFN + self.cFP ) / float( self.cTP + self.cTN + self.cFP + self.cFN )
        except ZeroDivisionError:
            self.cErrorRate = -1

        # F1-Measure.
        self.beta = 1.0
        # With beta=1 F-Measure is also Fscore
        try:
            self.fmeasure1 = ( ( (self.beta * self.beta) + 1 ) * self.Precision * self.TPR  ) / float( ( self.beta * self.beta * self.Precision ) + self.TPR )
        except ZeroDivisionError:
            self.fmeasure1 = -1
        try:
            self.cfmeasure1 = ( ( (self.beta * self.beta) + 1 ) * self.cPrecision * self.cTPR  ) / float( ( self.beta * self.beta * self.cPrecision ) + self.cTPR )
        except ZeroDivisionError:
            self.cfmeasure1 = -1

        # F2-Measure.
        self.beta = 2
        # With beta=2 F-Measure gives more importance to TPR (recall)
        try:
            self.fmeasure2 = ( ( (self.beta * self.beta) + 1 ) * self.Precision * self.TPR  ) / float( ( self.beta * self.beta * self.Precision ) + self.TPR )
        except ZeroDivisionError:
            self.fmeasure2 = -1
        try:
            self.cfmeasure2 = ( ( (self.beta * self.beta) + 1 ) * self.cPrecision * self.cTPR  ) / float( ( self.beta * self.beta * self.cPrecision ) + self.cTPR )
        except ZeroDivisionError:
            self.cfmeasure2 = -1

        # F0.5-Measure.
        self.beta = 0.5
        # With beta=2 F-Measure gives more importance to Precision
        try:
            self.fmeasure05 = ( ( (self.beta * self.beta) + 1 ) * self.Precision * self.TPR  ) / float( ( self.beta * self.beta * self.Precision ) + self.TPR )
        except ZeroDivisionError:
            self.fmeasure05 = -1
        try:
            self.cfmeasure05 = ( ( (self.beta * self.beta) + 1 ) * self.cPrecision * self.cTPR  ) / float( ( self.beta * self.beta * self.cPrecision ) + self.TPR )
        except ZeroDivisionError:
            self.cfmeasure05 = -1

        # Mean squared error?



def plot(file, time_window, comparison_type, time_windows_group):
    """
    For ploting the performance metrics of all methods. time_window and file are only for the title.
    """
    try:
        import matplotlib.pyplot as plt
        global time_window_id # Here it is equal to the amount of time windows
        global plot_file
        global alpha

        if debug:
            print ' > Plotting the metrics...'

        # It does not catch up things like 0.4%
        percentage_of_the_file_tested = ""

        # We should plot all the metrics against the number of interval. From 1 
        range_time_windows = range(1, time_window_id + 1)
        
        if comparison_type == 'time':
            # We only work with bclus and CAMNEP here, we can not plot everything.
            clusterAlg = time_windows_group[-1].algorithms_dict['Bclus']
            #camnepAlg = time_windows_group[-1].algorithms_dict['MasterAggregator-1.00']

            # General plot
            ax = plt.subplot(111)
            #plt.plot(range_time_windows, clusterAlg.plotfmeasure2,'b-', range_time_windows, camnepAlg.plotfmeasure2,'r-', range_time_windows, clusterAlg.plotfmeasure1, 'b--', range_time_windows, camnepAlg.plotfmeasure1, 'r--', range_time_windows, clusterAlg.plotFPR, 'b-.', range_time_windows, camnepAlg.plotFPR, 'r-.', range_time_windows, clusterAlg.plotTPR, 'b:', range_time_windows, camnepAlg.plotTPR, 'r:', range_time_windows, clusterAlg.plotfmeasure05,'g-', range_time_windows, camnepAlg.plotfmeasure05,'c-')
            plt.plot(range_time_windows, clusterAlg.plotfmeasure2,'b-', range_time_windows, clusterAlg.plotfmeasure1, 'b--', range_time_windows, clusterAlg.plotFPR, 'b-.', range_time_windows, clusterAlg.plotTPR, 'b:',  range_time_windows, clusterAlg.plotfmeasure05,'g-')
            plt.legend(('Bclus Fm2', 'CAMNEP Fm2', 'Bclus Fm1', 'CAMNEP Fm1', 'Bclus FPR', 'CAMNEP FPR', 'Bclus TPR', 'CAMNEP TPR', 'Bclus Fm05', 'CAMNEP Fm05'), 'upper center', shadow=True, fancybox=True)
            plt.title('Performance Metrics comparison for '+ str(time_window) + ' seconds.')


        elif comparison_type == 'weight':
            # We only work with bclus and CAMNEP here, we can not plot everything.
            clusterAlg = time_windows_group[-1].algorithms_dict['Bclus']
            #camnepAlg = time_windows_group[-1].algorithms_dict['MasterAggregator-1.00']
            allpositiveAlg = time_windows_group[-1].algorithms_dict['AllPositive']
            # General plot
            ax = plt.subplot(111)
            #plt.plot(range_time_windows, clusterAlg.t_plotfmeasure2,'b-', range_time_windows, camnepAlg.t_plotfmeasure2,'r-', range_time_windows, clusterAlg.t_plotfmeasure1, 'b--', range_time_windows, camnepAlg.t_plotfmeasure1, 'r--', range_time_windows, clusterAlg.t_plotFPR, 'b-.', range_time_windows, camnepAlg.t_plotFPR, 'r-.', range_time_windows, clusterAlg.t_plotTPR, 'b:', range_time_windows, camnepAlg.t_plotTPR, 'r:', range_time_windows, clusterAlg.t_plotfmeasure05,'g-', range_time_windows, camnepAlg.t_plotfmeasure05,'c-')
            ##plt.plot(range_time_windows, clusterAlg.t_plotfmeasure1, 'b--', range_time_windows, camnepAlg.t_plotfmeasure1, 'r--', range_time_windows, clusterAlg.t_plotFPR, 'b-.', range_time_windows, camnepAlg.t_plotFPR, 'r-.', range_time_windows, clusterAlg.t_plotTPR, 'b:', range_time_windows, camnepAlg.t_plotTPR, 'r:')
            plt.plot(range_time_windows, clusterAlg.t_plotfmeasure1, 'b--', range_time_windows, clusterAlg.t_plotFPR, 'b-.', range_time_windows, clusterAlg.t_plotTPR, 'b:' )
            #plt.legend(('Bclus FM1', 'CAMNEP FM1', 'Bclus FPR', 'CAMNEP FPR', 'Bclus TPR', 'CAMNEP TPR'), 'upper center', shadow=True, fancybox=True)
            plt.legend(('Bclus FM1', 'Bclus FPR', 'Bclus TPR'), 'upper center', shadow=True, fancybox=True)
            plt.title('Performance Weighted Metrics comparison for ' + str(time_window) + ' seconds, alpha ' + str(alpha) + '.')

        plt.ylim(ymin=-0.01)
        plt.xlabel('Time window')
        plt.ylabel('%')
        plt.grid(True)

        # ROC plot
        """
        ay = plt.subplot(212)
        plt.plot(clusterAlg.plotFPR, clusterAlg.plotTPR, 'b-', camnepAlg.plotFPR, camnepAlg.plotTPR, 'r-')
        plt.legend(('Cluster', 'CAMNEP'), 'upper center', shadow=True, fancybox=True)
        plt.xlabel('FPR')
        plt.ylabel('TPR')
        plt.title('ROC')
        """
        if plot_file:
            plt.savefig(plot_file, bbox_inches=0, dpi=600)
        else:
            plt.show()


    except Exception as inst:
        if debug:
            print 'Some problem in plot()'
        print type(inst)     # the exception instance
        print inst.args      # arguments stored in .args
        print inst           # __str__ allows args to printed directly
        x, y = inst          # __getitem__ allows args to be unpacked directly
        print 'x =', x
        print 'y =', y
        exit(-1)





def  extract_columns(line, tw, file_format):
    """
    This function takes a line and extracts the columns. It returns the columns in a dictionary
    """
    try:
        global debug
        global verbose

        #if debug:
            #print ' > Extracting columns'
        
        columns = {} 


        if file_format == 'Netflow':
            # Columns are based on netflow standard
            columns['flow_time'] = line.split()[0]+' '+line.split()[1]

            # Src IP can have a : with the src port or not.
            columns['srcIP'] = line.split()[4]
            if ':' in columns['srcIP']:
                columns['srcIP'] = columns['srcIP'].split(':')[0]

            # Real label
            columns['real_label'] = line.split()[12]
        elif file_format == 'Argus':
            # Columns are based on some argus standard
            columns['flow_time'] = line.split(',')[0]

            # Src IP can have a : with the src port or not.
            columns['srcIP'] = line.split(',')[4]

            # Real label
            columns['real_label'] = line.split(',')[32].split('flow=')[1]

        # Store the amount of labels read
        try:
            tw.amount_of_labels[columns['real_label']] += 1
        except KeyError:
            tw.amount_of_labels[columns['real_label']] = 1
        if debug:
            print '  > Flow time:{0}, srcIP:{1}, Real Label:{2}'.format(columns['flow_time'],columns['srcIP'], columns['real_label'])

        # We shuld read each column based on the algorithm, extract the label and assign it.
        for algorithm_name in tw.algorithms_dict:
            # Predicted label
            try:
                # Normal algorithms
                if file_format == 'Netflow':
                    tw.algorithms_dict[algorithm_name].ip_current_labels[columns['srcIP']] = line.split()[tw.algorithms_dict[algorithm_name].headercolumn].strip('\n')
                elif file_format == 'Argus':
                    tw.algorithms_dict[algorithm_name].ip_current_labels[columns['srcIP']] = line.split(',')[tw.algorithms_dict[algorithm_name].headercolumn].strip('\n')
                if debug:
                    print '   > Extracting information for algorithm {0}. Label: {1}'.format(algorithm_name,tw.algorithms_dict[algorithm_name].ip_current_labels[columns['srcIP']])
            except TypeError:
                # Dummy algorithms
                # The header column is being used as predicted label for some dummy algorithm.
                tw.algorithms_dict[algorithm_name].ip_current_labels[columns['srcIP']] = tw.algorithms_dict[algorithm_name].headercolumn
                #if debug:
                    #print '   > Extracting information for dummy algorithm {0}. Label: {1}'.format(algorithm_name,tw.algorithms_dict[algorithm_name].ip_current_labels[columns['srcIP']])

        return columns

    except IndexError:
        print 'WARNING! It seems that some columns are missing!'
        exit(-1)

    except Exception as inst:
        if debug:
            print 'Some problem in extract_columns()'
        print type(inst)     # the exception instance
        print inst.args      # arguments stored in .args
        print inst           # __str__ allows args to printed directly
        x, y = inst          # __getitem__ allows args to be unpacked directly
        print 'x =', x
        print 'y =', y
        exit(-1)


def report_errors(tw):
    """
    This function is used when each time window ends. It takes every algorithm and print the errors to the screen. These are live metrics, not the final ones.
    """
    try:
        #global algorithms_dict
        global debug
        global verbose
        global comparison_type

        #B1 is when the predicted label was negative, and the real label was background.
        #print 'B1: Predicted negative, real background.'
        #B2 is when the predicted label was positive, and the real label was background.
        #print 'B2: Predicted positive, real background.'
        #B3 is when the predicted label was background, and the real label was negative.
        #print 'B3: Predicted background, real negative.'
        #B4 is when the predicted label was background, and the real label was positive.
        #print 'B4: Predicted background, real positive.'
        #B5 is when the predicted label was background, and the real label was background.
        #print 'B5: Predicted background, real background.'
        print

        # Find the longest algo name
        max_name_len = 0
        for i in tw.algorithms_dict:
            if len(i) > max_name_len:
                max_name_len = len(i)

        # Print the time window info
        print tw

        # Print the results of each algorithm
        if comparison_type == 'time':
            print '\n+ Current +'
            for algorithm_name in tw.algorithms_dict:
                tw.algorithms_dict[algorithm_name].current_reportprint(max_name_len)
            print '\n+ Cumulative +'
            for algorithm_name in tw.algorithms_dict:
                tw.algorithms_dict[algorithm_name].reportprint(max_name_len)
        elif comparison_type == 'weight':
            """
            print '\n+ Current Normal +'
            for algorithm_name in tw.algorithms_dict:
                tw.algorithms_dict[algorithm_name].current_reportprint(max_name_len)
            """
            print '\n+ Current Errors +'
            for algorithm_name in tw.algorithms_dict:
                tw.algorithms_dict[algorithm_name].current_reportprint(max_name_len)
            print '\n+ Current Weighted +'
            for algorithm_name in tw.algorithms_dict:
                tw.algorithms_dict[algorithm_name].weighted_current_reportprint(max_name_len)
            print '\n+ Cumulative Weighted +'
            for algorithm_name in tw.algorithms_dict:
                tw.algorithms_dict[algorithm_name].weighted_reportprint(max_name_len)
        print

    except Exception as inst:
        if debug:
            print 'Some problem in report_errors()'
        print type(inst)     # the exception instance
        print inst.args      # arguments stored in .args
        print inst           # __str__ allows args to printed directly
        x, y = inst          # __getitem__ allows args to be unpacked directly
        print 'x =', x
        print 'y =', y
        exit(-1)


def report_final_errors():
    """
    This function prints for each time window, the final results of each algorithm
    """
    try:
        global debug
        global verbose
        global time_windows_group
        global comparison_type
        global csv_file

        print '\n\n'
        print '[+] Final Error Reporting [+]'
        print '============================='

        if comparison_type == 'time':
            for algorithm_name in time_windows_group[-1].algorithms_dict:
                time_windows_group[-1].algorithms_dict[algorithm_name].reportprint(30)
            if csv_file:
                csv_handler = open(csv_file, 'a+')
                csv_handler.write('Name,TP,TN,FP,FN,TPR,TNR,FPR,FNR,Precision,Accuracy,ErrorRate,fmeasure1,fmeasure2,fmeasure05,B1,B2,B3,B4,B5\n')
                for algorithm_name in time_windows_group[-1].algorithms_dict:
                    time_windows_group[-1].algorithms_dict[algorithm_name].report_CSV_print(30,csv_handler)
                csv_handler.close()
        elif comparison_type == 'weight':
            print '\nCumulative Common errors'
            print '-------------------------'
            for algorithm_name in time_windows_group[-1].algorithms_dict:
                time_windows_group[-1].algorithms_dict[algorithm_name].reportprint(30)
            print '\nWeighted errors'
            print '----------------'
            for algorithm_name in time_windows_group[-1].algorithms_dict:
                time_windows_group[-1].algorithms_dict[algorithm_name].weighted_reportprint(30)
            if csv_file:
                csv_handler = open(csv_file, 'a+')
                csv_handler.write('Name,t_TP,t_TN,t_FP,t_FN,t_TPR,t_TNR,t_FPR,t_FNR,t_Precision,t_Accuracy,t_ErrorRate,t_fmeasure1,t_fmeasure2,t_fmeasure05,t_B1,t_B2,t_B3,t_B4,t_B5\n')
                for algorithm_name in time_windows_group[-1].algorithms_dict:
                    time_windows_group[-1].algorithms_dict[algorithm_name].weighted_report_CSV_print(30,csv_handler)
                csv_handler.close()

    except Exception as inst:
        if debug:
            print 'Some problem in report_final_errors()'
        print type(inst)     # the exception instance
        print inst.args      # arguments stored in .args
        print inst           # __str__ allows args to printed directly
        x, y = inst          # __getitem__ allows args to be unpacked directly
        print 'x =', x
        print 'y =', y
        exit(-1)



def generate_algorithms(headersline, tw, file_format):
    """ Generate all the algorithms objects. One for each column in the file """
    try:
        global debug
        global verbose
        #global algorithms_dict

        temp_real_negative_label = ''
        temp_real_positive_label = ''
        temp_real_background_label = ''

        if debug:
            print ' > Headers line read: {0}'.format(headersline)

        # Find algorithms names and number by reading the first line.
        if file_format == 'Netflow':
            split_headers = headersline.split()[12:]
        if file_format == 'Argus':
            split_headers = headersline.split(',')[32:]
        
        for algorithm_header in split_headers:
            if debug:
                print '  >> Algorithm header read: {0}'.format(algorithm_header)
            algorithm_name = algorithm_header.split('(')[0]
            if file_format == 'Netflow':
                algorithm_headercolumn = split_headers.index(algorithm_header) + 12
            elif file_format == 'Argus':
                algorithm_headercolumn = split_headers.index(algorithm_header) + 32
            try:
                algorithm_negative_label = algorithm_header.split('(')[1].split(')')[0].split(':')[0]
                algorithm_positive_label = algorithm_header.split('(')[1].split(')')[0].split(':')[1]
            except IndexError:
                # This column is not a column with labels because it does not have the ()
                continue

            try:
                algorithm_background_label = algorithm_header.split('(')[1].split(')')[0].split(':')[2]
            except IndexError:
                # There is no background label for this algorithm
                algorithm_background_label = ''

            if debug:
                print '    > Algorithm name: {0} (column {3}). Positive label: {1}, Negative Label: {2}, Background Label: {4}'.format(algorithm_name, algorithm_positive_label, algorithm_negative_label, algorithm_headercolumn, algorithm_background_label)

            # Manage the real labels in the file
            if 'label' in algorithm_name.lower():
                if debug:
                    print '    > Generating the real labels.'
                # Store the real labels for later
                temp_real_positive_label = algorithm_positive_label
                temp_real_negative_label = algorithm_negative_label
                temp_real_background_label = algorithm_background_label
                continue

            # Create the algorithm object
            temp_algorithm = algorithm()
            temp_algorithm.name = algorithm_name
            temp_algorithm.headercolumn = algorithm_headercolumn
            # Negative predicted label
            temp_algorithm.algorithm_labels[0] = algorithm_negative_label
            # Positive predicted label
            temp_algorithm.algorithm_labels[1] = algorithm_positive_label
            # Background predicted label
            temp_algorithm.algorithm_labels[2] = algorithm_background_label
            # Real negative label
            temp_algorithm.real_labels[0] = temp_real_negative_label
            # Real positive label
            temp_algorithm.real_labels[1] = temp_real_positive_label
            # Real background label
            temp_algorithm.real_labels[2] = temp_real_background_label

            # Store it in the global dict
            newalgorithm = copy.deepcopy(temp_algorithm)
            tw.algorithms_dict[newalgorithm.name] = newalgorithm

        # End for


        # Create the dummy algorithm that predicts everything as a Botnet
        temp_algorithm = algorithm()
        temp_algorithm.name = 'AllPositive'
        # For these dummy algorithms, the headercolumn is used as predicted label. Because they do not exist in the netflow overall table.
        temp_algorithm.headercolumn = temp_real_positive_label
        # Negative predicted label
        temp_algorithm.algorithm_labels[0] = 'Not Defined'
        # Positive predicted label
        temp_algorithm.algorithm_labels[1] = temp_real_positive_label
        # Background predicted label
        temp_algorithm.algorithm_labels[2] = 'Not Defined'
        # Real negative label
        temp_algorithm.real_labels[0] = temp_real_negative_label
        # Real positive label
        temp_algorithm.real_labels[1] = temp_real_positive_label
        # Real background label
        temp_algorithm.real_labels[2] = temp_real_background_label
        # Store it in the global dict
        newalgorithm = copy.deepcopy(temp_algorithm)
        tw.algorithms_dict[newalgorithm.name] = newalgorithm


        # Create the dummy algorithm that predicts everything as Normal
        temp_algorithm = algorithm()
        temp_algorithm.name = 'AllNegative'
        # For these dummy algorithms, the headercolumn is used as predicted label. Because they do not exist in the netflow overall table.
        temp_algorithm.headercolumn = temp_real_negative_label
        # Negative predicted label
        temp_algorithm.algorithm_labels[0] = temp_real_negative_label
        # Positive predicted label
        temp_algorithm.algorithm_labels[1] = 'Not Defined'
        # Background predicted label
        temp_algorithm.algorithm_labels[2] = 'Not Defined'
        # Real negative label
        temp_algorithm.real_labels[0] = temp_real_negative_label
        # Real positive label
        temp_algorithm.real_labels[1] = temp_real_positive_label
        # Real background label
        temp_algorithm.real_labels[2] = temp_real_background_label
        # Store it in the global dict
        newalgorithm = copy.deepcopy(temp_algorithm)
        tw.algorithms_dict[newalgorithm.name] = newalgorithm

        # Create the dummy algorithm that predicts everything as Background
        temp_algorithm = algorithm()
        temp_algorithm.name = 'AllBackground'
        # For these dummy algorithms, the headercolumn is used as predicted label. Because they do not exist in the netflow overall table.
        temp_algorithm.headercolumn = temp_real_background_label
        # Negative predicted label
        temp_algorithm.algorithm_labels[0] = 'Not Defined'
        # Positive predicted label
        temp_algorithm.algorithm_labels[1] = 'Not Defined'
        # Background predicted label
        temp_algorithm.algorithm_labels[2] = temp_real_background_label
        # Real negative label
        temp_algorithm.real_labels[0] = temp_real_negative_label
        # Real positive label
        temp_algorithm.real_labels[1] = temp_real_positive_label
        # Real background label
        temp_algorithm.real_labels[2] = temp_real_background_label
        # Store it in the global dict
        newalgorithm = copy.deepcopy(temp_algorithm)
        tw.algorithms_dict[newalgorithm.name] = newalgorithm

        if debug:
            print 'End generating the algorithms...\n'

    except Exception as inst:
        if debug:
            print 'Some problem in generate_algorithms'
        print type(inst)     # the exception instance
        print inst.args      # arguments stored in .args
        print inst           # __str__ allows args to printed directly
        x, y = inst          # __getitem__ allows args to be unpacked directly
        print 'x =', x
        print 'y =', y
        exit(-1)


def process_file(file, comparison_type, time_window): 
    """
    This function takes a file, time window and comparison type and generates the staditistics of the detection performance of every algorithm. Type can be 'flow' based or 'time' based. 
    """
    try:
        global debug
        global verbose
        global time_window_id
        global time_windows

        processing_init_time = datetime.now()

        if debug:
            print 'Processsing file...'

        # Open the file for reading
        f = open(file,'r')

        # Read the first line. The headers line...
        line = f.readline()

        if line[0] != '#':
            print
            print 'WARNING! The first line must be commented with #, and be the headers line!!!'
            print
            exit(-1)


        # Find out if the columns are space separated or comma separated
        if len(line.split()) > len(line.split(',')):
            # Space separated. This means the old netflow format
            file_format = 'Netflow'
            if debug:
                print 'Netflow file format. Space separated'
        else:
            # Comma separated. This means the new biargus format
            file_format = 'Argus'
            if debug:
                print 'Argus file format. Comma separated'

        # Create an empty time window. For the flow-by-flow analysis this is the only time window. For the time-based analysis it is the first
        tw = time_windows()

        # Clean the algorithms ip labels
        tw.clean_ip_labels()

        # Generate the algorithms objects and identify the columns
        generate_algorithms(line, tw, file_format)

        # Read the second line. 
        line = f.readline()

        # If comparison is flow based...
        if comparison_type == 'flow':
            if debug:
                print 'Comparing labels flow by flow...'
                print 'Using file {0}.'.format(file)

            # We already read two lines
            tw.lines_read = 1

            while (line):
                # No comments
                if line[0] == '#':
                    try:
                        line = f.readline()
                        while (line[0]=='#'):
                            line = f.readline()
                    except IndexError:
                        # The file can end with comments
                        continue

                #if debug:
                    #print '>-------------\n> Reading line:{0}'.format(line)


                # Extract the columns correctly
                columns = extract_columns(line,tw, file_format)

                # Compute the error with the predicted label and the real label
                for algorithm_name in tw.algorithms_dict:
                    try:
                        predicted_label = tw.algorithms_dict[algorithm_name].ip_current_labels[columns['srcIP']]
                        tw.algorithms_dict[algorithm_name].compute_error(predicted_label, columns['real_label'])

                    except KeyError:
                        # The algorithm does not have any predicted label.
                        continue

                # Read next line
                line = f.readline()
                tw.lines_read = tw.lines_read + 1


            # Last line is empty
            tw.lines_read = tw.lines_read - 1

            # Verify the amount of labels.
            total = 0
            for label in tw.amount_of_labels:
                total = total + tw.amount_of_labels[label]
            if tw.lines_read != total:
                print
                print 'WARNING! The amount of labels read is not the same that the amount of labels in the file.'
                print 'Lines read: {0}'.format(tw.lines_read)
                for label in tw.amount_of_labels:
                    print 'Amount of {0} labels: {1}'.format(label, tw.amount_of_labels[label])
                print 'Total amount of labels: {0}'.format(total)
                exit(-1)

            # Report errors
            report_errors(tw)



        # If comparison is time based or weight based...
        elif comparison_type == 'time' or comparison_type == 'weight':
            if debug:
                print '\nComparing labels flows using a ' + str(time_window) + ' seconds time window.'
                print 'Using file {0}.'.format(file)

            # Store the time windows in the vector
            time_windows_group.append(tw)

            # Link the algorithms dict with the time window, so we can access the info from the tw
            #tw.algorithms_dict = algorithms_dict


            # No comments
            if line[0] == '#':
                line = f.readline()
                while (line[0]=='#'):
                    line = f.readline()

            # Get the start time
            # our flows times are like this: 2011-08-16 10:30:00.081
            if file_format == 'Netflow':
                time_window_flow_start_time = datetime.strptime(line.split()[0]+' '+line.split()[1], "%Y-%m-%d %H:%M:%S.%f")
            elif file_format == 'Argus':
                time_window_flow_start_time = datetime.strptime(line.split(',')[0], "%Y/%m/%d %H:%M:%S.%f")

            while (line):

                # Do not read comments
                if line[0] == '#':
                    line = f.readline()
                    continue

                # Current time
                if file_format == 'Netflow':
                    current_flow_start_time =  datetime.strptime(line.split()[0]+' '+line.split()[1], "%Y-%m-%d %H:%M:%S.%f")
                elif file_format == 'Argus':
                    current_flow_start_time =  datetime.strptime(line.split(',')[0], "%Y/%m/%d %H:%M:%S.%f")

                # Compute the difference
                delta_time = current_flow_start_time - time_window_flow_start_time
                    #print ' > Current labels: original= {0}. srcIP={1}. Algorithms: {2}'.format(columns['real_label'], columns['srcIP'], tw.algorithms_labels_for_this_ip(columns['srcIP']) )

                # Differentiate between the time windows. Only < and not <=.
                if delta_time.total_seconds() < time_window:
                    # We are inside the specified time window
                    #if debug:
                        #print '> -------------\n> Reading line in this time window: {0}'.format(line.strip())
                        #print ' > Delta time: {0} (time window={1})'.format(delta_time.total_seconds(),time_window)
                        #print ' Inside the current time windows.'


                    # Extract the columns correctly
                    columns = extract_columns(line, tw, file_format)

                    tw.lines_read = tw.lines_read + 1


                    # Add the label for the current ip. Check uniqueness.
                    tw.add_ip_label(columns['srcIP'], columns['real_label'])

                    # Read next line. This should be inside this if, and not outside. Otherwise we lose the last line read.
                    line = f.readline()

                else:
                    # We are outside the time window

                    #if debug:
                    #    print '> -------------\n> Reading line outside this time window: {0}'.format(line)
                    #print ' > Delta time: {0} (time window={1})'.format(delta_time.total_seconds(),time_window)

                    if debug:
                        print ' > Analyzing the time window {0}'.format(tw.id)

                    # We should compute errors for EACH IP address seen...
                    tw.compute_errors()

                       
                    ###############################################
                    # If in weighted mode, compute the weight errors
                    if comparison_type == 'weight':
                        tw.compute_weighted_errors()
                    ###############################################

                    #print '\nAmount of ips in the time window number {1}: {0}'.format(tw.amount_of_ips, tw.id)
                    report_errors(tw)

                    # Update the ploting values for each algorithm. This way we have one value each time the time windows ends.
                    ###############################################
                    # If in weighted mode, compute the weight errors
                    if comparison_type == 'weight':
                        for alg in tw.algorithms_dict:
                            tw.algorithms_dict[alg].update_weighted_plot()
                    elif comparison_type == 'time':
                        for alg in tw.algorithms_dict:
                            tw.algorithms_dict[alg].updateplot()
                    ###############################################

                    # New time window start time
                    if file_format == 'Netflow':
                        time_window_flow_start_time = datetime.strptime(line.split()[0]+' '+line.split()[1], "%Y-%m-%d %H:%M:%S.%f")
                    elif file_format == 'Argus':
                        time_window_flow_start_time = datetime.strptime(line.split(',')[0], "%Y/%m/%d %H:%M:%S.%f")

                    # Store the algorithms names for the next time window
                    temp_algorithms = copy.deepcopy(tw.algorithms_dict)

                    # Create the next time window object
                    tw = time_windows()
    
                    # Copy the algorithms to the next time window
                    tw.algorithms_dict = temp_algorithms

                    # We should empty the dictionaries
                    tw.clean_ip_labels()

                    # Store the time windows in the vector
                    time_windows_group.append(tw)

            # Here we are out of the while

            # Check if there are still IPs that were not analyzed. 
            # It is the case when the file ends during the time window and we did not process the last lines of the last time window.
            # In short, we did not go into the 'the time windows ended' part.

            if tw.ip_original_labels:
                if debug:
                    print '> There were still some lines not processed because the file ended but not the time window.'
                # The las line belongs to this time window
                tw.lines_read = tw.lines_read + 1

                # There is still something in the dictionary! process it.
                tw.compute_errors()

                #if verbose:
                    #print '\nAmount of ips in the time window number {1}: {0}'.format(tw.amount_of_ips, tw.id)
                    #report_errors(tw)

                ###############################################
                # If in weighted mode, compute the weight errors
                if comparison_type == 'weight':
                    tw.compute_weighted_errors()
                ###############################################

                # Update the ploting values for each algorithm. This way we have one value each time the time windows ends.
                ###############################################
                # If in weighted mode, compute the weight errors
                if comparison_type == 'weight':
                    for alg in tw.algorithms_dict:
                        tw.algorithms_dict[alg].update_weighted_plot()
                elif comparison_type == 'time':
                    for alg in tw.algorithms_dict:
                        tw.algorithms_dict[alg].updateplot()
                ###############################################


            # Last line is empty
            tw.lines_read = tw.lines_read - 1

            #print
            #print '++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++'
            #print
            #print 'Lines read: {0}'.format(tw.lines_read)
            #print 'Amount of normal labels: {0}'.format(tw.amount_of_labels)
            #print 'Amount of time windows: {0}\n'.format(tw.id)
            #print 'Time window width: {0}\n'.format(time_window)

            # Report errors
            report_errors(tw)
       

        # After the ifs, we now have to compute the final metrics
        report_final_errors()


        # Processing time computing
        processing_finish_time = datetime.now()
        delta = processing_finish_time - processing_init_time
        print '\nProcessing lasted {0} seconds'.format(delta.seconds)



    except Exception as inst:
        if debug:
            print 'Some problem in process_file()'
        print type(inst)     # the exception instance
        print inst.args      # arguments stored in .args
        print inst           # __str__ allows args to printed directly
        x, y = inst          # __getitem__ allows args to be unpacked directly
        print 'x =', x
        print 'y =', y
        exit(-1)




def main():
    try:
        global debug
        global verbose
        global doplot
        global alpha
        global comparison_type
        global time_windows_group
        global csv_file
        global out_file
        global plot_file

        file = ""
        comparison_type = ""
        time_window = 0

        opts, args = getopt.getopt(sys.argv[1:], "a:c:VvDhf:t:T:pP:o:", ["alpha=","csv=", "help","version","verbose","debug","file=","type=", "time=", "plot", "plot-to-file=", "out="])
    except getopt.GetoptError: usage()

    for opt, arg in opts:
        if opt in ("-h", "--help"): usage()
        if opt in ("-V", "--version"): version();exit(-1)
        if opt in ("-v", "--verbose"): verbose=True
        if opt in ("-D", "--debug"): debug=1
        if opt in ("-f", "--file"): file=arg
        if opt in ("-t", "--type"): comparison_type=arg
        if opt in ("-T", "--time"): time_window = float(arg) 
        if opt in ("-p", "--plot"): doplot = True
        if opt in ("-a", "--alpha"): alpha = float(arg)
        if opt in ("-c", "--csv"): csv_file = str(arg)
        if opt in ("-o", "--out"): out_file = str(arg)
        if opt in ("-P", "--plot-to-file"): plot_file = str(arg)
    try:
        try:
            if debug:
                verbose = True

            if file == "" or comparison_type == "":
                usage()
                sys.exit(1)


            # Direct process of netflow flows
            elif file != "" and ( comparison_type == "flow" or ( comparison_type == "time" and time_window != 0 ) or ( comparison_type == "weight" and time_window != 0 )):
                # Output everything to a file
                if out_file:
                    tee = subprocess.Popen(["tee", out_file], stdin=subprocess.PIPE)
                    os.dup2(tee.stdin.fileno(), sys.stdout.fileno())
                    os.dup2(tee.stdin.fileno(), sys.stderr.fileno())

                version()
                process_file(file, comparison_type, time_window)
                if doplot:
                    plot(file, time_window, comparison_type, time_windows_group)

            else:
                usage()
                sys.exit(1)

        except Exception, e:
                print "misc. exception (runtime error from user callback?):", e
        except KeyboardInterrupt:
                sys.exit(1)


    except KeyboardInterrupt:
        # CTRL-C pretty handling.
        print "Keyboard Interruption!. Exiting."
        sys.exit(1)


if __name__ == '__main__':
    main()

