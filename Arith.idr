module SpecD

-- Provide a placeholder type for a spectrogram
SpectTy : Type 
SpectTy = Nat 

-- Datatype to track whether we should be returning a residual 
data ResidualTy = Residual | Pair 

-- Transform ResidualTy to a type that we can return 
decompTy : ResidualTy -> Type 
decompTy Residual = (SpectTy, SpectTy, SpectTy)
decompTy Pair = (SpectTy, SpectTy)

-- Fix a threshold for when we should return a 2-tuple, or a 3-tuple
threshold : Nat 
threshold = 10 

-- Figure out which kind of residual type we should be returning, based on a threshold
whichTy : (t: Nat) -> (n: Nat) -> ResidualTy
whichTy Z Z = Residual -- Equal to the the threshold, i.e. we should have a residual 
whichTy Z (S k) = Residual -- Greater than the threshold
whichTy (S k) Z = Pair -- Less than threshold 
whichTy (S k) (S j) = whichTy k j -- recurse 

-- Decomposition implementation
decomp_impl : (s: SpectTy) -> (n: Nat) -> (r: ResidualTy) -> decompTy r
decomp_impl s n Residual = (s *1, s*2, s*n)
decomp_impl s n Pair = (s *1, s* 2)

-- Decomposition interface 
decompose : (s: SpectTy) -> (n: Nat) -> (decompTy (whichTy SpecD.threshold n))
decompose s n = decomp_impl s n (whichTy SpecD.threshold n)
