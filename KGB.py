import pandas as pd

import numpy as np

from scipy.stats import entropy
import time
from sklearn.decomposition import PCA


def preprocess_df(df): 
    """
    Run preprocessing operations

    Parameters
    ----------
    df : Pandas DataFrame
        

    Returns
    -------
    df : Pandas DataFrame
        preprocessed df

    """
    # fill nan values in order to have only integers in Ports columns
    df['Sport'] = df['Sport'].fillna(-1)
    df['Dport'] = df['Dport'].fillna(-1)
    
    # Extract labels
    df["Backgroung_label"] = df.Label.str.contains("Background")
    df["Normal_label"] = df.Label.str.contains("Normal")
    df["Botnet_label"] = df.Label.str.contains("Botnet")
    
    # Convert time column to a proper format
    df["StartTime"] = pd.to_datetime(df["StartTime"])
    # sort by time 
    df.sort_values("StartTime", inplace = True)
    return df


def compute_contexte_vector(df, window_size = 1, window_count = 5, verbose = False, fillna= True):
    """
    Given a window size, compute the context feature for the last minutes of the dataset

    Parameters
    ----------
    df : Pandas DataFrame
        Must contain at least enough minutes of data considering window sizes. 
        Only the last minutes will be considered
    window_size : int, optional
        Duration in minutes of the window. The default is 1.
    window_count : int, optionnal
        Count of Windows in the context vector. The default is 5
    verbose : boolean, optional
        if you want more details. The default is False.

    Returns
    -------
    futur_df : Pandas DataFrame
        The context Vector

    """
    # useful columns
    to_keep = ["StartTime","SrcAddr","DstAddr","Sport", "Dport","Label","Backgroung_label","Normal_label","Botnet_label"]
    df_for_entropies = df[to_keep]
    
    # Considered minutes
    last_time = df_for_entropies.StartTime.max()
    time_min = last_time - pd.Timedelta(f"{window_size + window_count -1} minutes")
    df_for_entropies = df_for_entropies[df_for_entropies.StartTime>=time_min] # we only keep the last minutes


    tmp_mesure = time.time_ns()
    base = 10
    entropy_agg =  lambda x : entropy(x.value_counts(), base=base) # Entropy computing method
    futur_df = pd.DataFrame({"SrcIP" : df_for_entropies.SrcAddr.unique()}).set_index("SrcIP") # initiate index column
    
    for i in range(window_count) : # for each window 
        start = time_min + pd.Timedelta(f"{i} minutes") # beginning timestamp
        end = start + pd.Timedelta(f"{window_size} minutes") # ending timestamp
        # get the raw vector for the window
        current_window = df_for_entropies[(df_for_entropies.StartTime>=start) & (df_for_entropies.StartTime<end)]
        
        # compute entropies
        df_with_Entropies = current_window.groupby(by = "SrcAddr").agg({'DstAddr': entropy_agg,
                                                                                'Dport': entropy_agg,
                                                                                 'Sport': entropy_agg})
        # rename the columns
        id_name = window_count-i-1
        df_with_Entropies.rename(columns = {"DstAddr" : f"H_DstAddr_t_{id_name}",
                                            "Dport" : f"H_Dport_t_{id_name}",
                                            "Sport" : f"H_Sport_t_{id_name}"}, inplace = True)
        # store the new columns
        futur_df = futur_df.merge(df_with_Entropies, left_index = True, right_index = True, how = "outer")
        
    if verbose : 
        print(f"Time required to compute aggregation : {np.round((time.time_ns() - tmp_mesure)/(10**9),2)} s")


    # If we have no value in a winodw for a specific IP source, we will obtain a nan
    # we replace it by a 0
    futur_df = futur_df.fillna(0)  
    
    return futur_df


def compute_pca_over_vector(df, drop_limit = 10**-6):
    """
    compute the PCA over the context vectors

    Parameters
    ----------
    df : Pandas DataFrame
        Context Vector
    drop_limit : float, optional
        We drop eigen vector/values below that limit. The default is 10**-6.(cf paper)

    Returns
    -------
    new_df : DataFrame Pandas
        Projected context vectors in the PCA space
    eigen_values_vectors : list of tuples 
        Contains eigen values & vectors such that each element is 
        (eigen_value, eigen_vector) where eigen_vector is a 1D array

    """
    
    pca = PCA()
    new_flows = pca.fit_transform(df) # project the context vector in the PCA space
    
    cov_matrix= pca.get_covariance() # Compute covariance matrix

    eigen_values_vectors = []
    for i, eigenvector in enumerate(pca.components_): # for each eigen vector

        eigen_value = np.dot(eigenvector.T, np.dot(cov_matrix, eigenvector)) # we compute the eigen value
        
        if eigen_value <  drop_limit : # if the eigen value is too low, drop
            break

        eigen_values_vectors.append((eigen_value,eigenvector)) # we store the eigen value & vector
        
    
    # Convert the projected context vector in DataFrame
    new_df = pd.DataFrame(new_flows[:,:i+1],columns = [f"component_{j}" for j in range(i+1)])
    new_df.set_index(df.index, drop = True, inplace = True)
    
    
    return new_df, eigen_values_vectors
           

def compute_anomaly_score(row, eigen, major_components = True,k=1):
    """
    Considering the eigen values and a context vector, 
    computes the anomaly score of the current vector

    Parameters
    ----------
    row : DataFrame row
        the current vector
    eigen : list of tuples
        contains eigen values & eigen vectors
    major_components : boolean, optional
        Set to True if we only consider major components. The default is True.
    k : int, optional
        Number of principal component to consider. The default is 1. (cf paper)

    Returns
    -------
    value_sum : float
        Anomaly score for the current vector

    """

    if major_components : 
        start = 1 # then we consider from the 1rst component
        end = k # to the k-th component
        
    else :
        start = k+1 # then we consider from the k+1-th component
        end = len(eigen) # to the last component
        
    value_sum = 0
    for j in range(start,end+1) : # for each considered component
        
        e_val, e_vec = eigen[j-1] # get eigen value & eigen vector

        val = np.dot(e_vec,np.array(row.values)) # vector product yj * xt
        
        val/=e_val # division by lambda_j
        val=val**2
        value_sum+=val # the sum
    
    return value_sum


def proceed_KGB(df, anomaly_threshold = 0, window_count = 5, window_size = 1,
                drop_limit_eigen = 10**-6,
                major_components = True,k=1
               ) :
    """
    run each step of the KGB algorithm

    Parameters
    ----------
    df : DataFrame Pandas
        Must contain at least enough minutes of data considering window sizes. 
        Only the last minutes will be considered
    anomaly_threshold : float, optional
        anomaly score minimal value. The default is 0.
    window_size : int, optional
        Duration in minutes of the window. The default is 1.
    window_count : int, optionnal
        Count of Windows in the context vector. The default is 5
    drop_limit_eigen : float, optional
        We drop eigen vector/values below that limit. The default is 10**-6.(cf paper).
        Supposed to be useful in order to maintain numerical stability.
    major_components : boolean, optional
        Set to True if we only consider major components. The default is True.
    k : TYPE, optional
        Number of principal component to consider. The default is 1. (cf paper)

    Returns
    -------
    res : DataFrame Pandas
        Df with anomaly scores

    """
    # Compute context vectors
    context = compute_contexte_vector(df, window_count = window_count, window_size = window_size)
    
    # Compute eigen values & eigen vectors
    new_components, eigen_values_vectors = compute_pca_over_vector(context, drop_limit = drop_limit_eigen)  
    
    # compute anomaly score for each row
    res = context.apply(lambda x: compute_anomaly_score(x,eigen_values_vectors,major_components = major_components, k=k  ),
                                        axis = 1)
    #return res.sort_values(ascending=False)
    
    #return [ index for index, row in res.iteritems() if row>anomaly_threshold]
    # remove lowest anomaly scores
    res = res[res>=anomaly_threshold]
    return res

